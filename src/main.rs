#![allow(dead_code)]
#![allow(unused_variables)]
#![allow(unused_assignments)]

use capstone::arch::arm64::ArchMode;
use capstone::prelude::*;
use capstone::Endian;
use object::{Object, ObjectSegment, ObjectSymbol};
use std::collections::{HashMap, HashSet, VecDeque};
use std::fs::{self, File};
use std::io::{self, BufWriter, Read, Write};
use std::process::Command;
use std::sync::{Arc, Mutex, mpsc};
use std::thread;
use std::time::Instant;

use unicorn_engine::unicorn_const::{Arch, HookType, Mode, Prot};
use unicorn_engine::{RegisterARM64, Unicorn};

// ДОБАВИЛ CircleShape, Shape и Transformable для отрисовки светодиодов
use sfml::graphics::{Color, RenderTarget, RenderWindow, Sprite, Texture, CircleShape, Shape, Transformable, RectangleShape};
use sfml::window::{Event, Style};

const ELF_FILE: &str = "nuttx";
const LOG_FILE: &str = "log.txt";

const UART0_BASE: u64 = 0x01c28000;
const UART_RANGE: u64 = 0x1000;
const MMIO_BASE: u64 = 0x01000000;
const MMIO_SIZE: u64 = 0x03000000;
const GICD_BASE: u64 = 0x01C81000;
const GICC_BASE: u64 = 0x01C82000;
const GIC_IAR: u64 = GICC_BASE + 0x0C;
const GIC_EOIR: u64 = GICC_BASE + 0x10;
const GICC_CTLR: u64 = GICC_BASE + 0x00;
const GICC_RPR: u64 = GICC_BASE + 0x14;
const GICC_HPPIR: u64 = GICC_BASE + 0x18;
const GICD_ISENABLER: u64 = GICD_BASE + 0x100;

// АДРЕС НАШИХ АППАРАТНЫХ СВЕТОДИОДОВ
const LED_BASE: u64 = 0x02000000;

const TIME_WARP_MULTIPLIER: u64 = 20; 
const NEVER_REACH_ADDR: u64 = 0xFFFFFFF0;
const MAX_INSN_LIMIT: u64 = 10_000_000_000;

const FB_BASE: u64 = 0x10000000;
const FB_WIDTH: usize = 320;
const FB_HEIGHT: usize = 240;
const FB_SIZE: usize = FB_WIDTH * FB_HEIGHT * 4; 

// УВЕЛИЧИВАЕМ ОКНО, чтобы влезла "Плата" под экраном
const WINDOW_WIDTH: u32 = 320;
const WINDOW_HEIGHT: u32 = 290;

struct LogFilter { writer: BufWriter<File> }

impl LogFilter {
    fn new(file: File) -> Self { Self { writer: BufWriter::new(file) } }
    fn log(&mut self, msg: &str) {
        let _ = writeln!(self.writer, "{}", msg);
        let _ = self.writer.flush();
    }
}

#[derive(Clone, Copy, PartialEq)]
enum SysReg {
    VbarEl1, ElrEl1, SpsrEl1, SpEl0, Fpcr, Fpsr, TpidrEl1, TpidrEl0, TpidrroEl0, 
    CntvCval, CntvTval, CntvCtl, CntpCval, CntpTval, CntpCtl, Daif, CpacrEl1, 
    SctlrEl1, TcrEl1, Cntpct, Cntvct, CurrentEl, Cntfrq, EsrEl1, FarEl1, DczidEl0, Midr, Unknown
}

#[derive(Clone, Copy)]
enum Action {
    Ignore, DaifSet(u64), DaifClr(u64), Msr(RegisterARM64, SysReg), Mrs(RegisterARM64, SysReg), DcZva(RegisterARM64),
}

struct EmuState {
    insn_count: u64,
    vbar_el1: u64, elr_el1: u64, spsr_el1: u64, pstate_daif: u64, esr_el1: u64, far_el1: u64, 
    tpidr_el1: u64, tpidr_el0: u64, tpidrro_el0: u64, cntv_cval: u64, cntv_ctl: u64, cpacr_el1: u64, sctlr_el1: u64, tcr_el1: u64,
    sp_el0: u64, fpcr: u64, fpsr: u64,
    uart_lcr: u8, uart_dll: u8, uart_dlh: u8, uart_ier: u8, tx_irq_pending: bool,
    rx_receiver: mpsc::Receiver<u8>, rx_fifo: VecDeque<u8>,
    gic_enabled: bool, interrupts_enabled: HashSet<u32>, active_irq: i32, timer_pending: bool,
    skip_functions: HashSet<u64>, mmio_state: HashMap<u64, u32>, mmio_reads: HashMap<u64, u32>,
    insn_cache: HashMap<u32, Action>,
    log_filter: Arc<Mutex<LogFilter>>,
}

impl EmuState {
    fn new(rx_receiver: mpsc::Receiver<u8>, log_filter: Arc<Mutex<LogFilter>>) -> Self {
        Self {
            insn_count: 0,
            vbar_el1: 0, elr_el1: 0, spsr_el1: 0x05, pstate_daif: 0x3C0, esr_el1: 0, far_el1: 0,
            tpidr_el1: 0, tpidr_el0: 0, tpidrro_el0: 0, cntv_cval: u64::MAX, cntv_ctl: 0, cpacr_el1: 0x300000, sctlr_el1: 0, tcr_el1: 0,
            sp_el0: 0, fpcr: 0, fpsr: 0,
            uart_lcr: 0x03, uart_dll: 0x0D, uart_dlh: 0x00, uart_ier: 0, tx_irq_pending: false,
            rx_receiver, rx_fifo: VecDeque::new(),
            gic_enabled: true, interrupts_enabled: HashSet::new(), active_irq: -1, timer_pending: false,
            skip_functions: HashSet::new(), mmio_state: HashMap::new(), mmio_reads: HashMap::new(),
            insn_cache: HashMap::new(),
            log_filter
        }
    }
}

fn parse_reg(name: &str) -> Option<RegisterARM64> {
    match name.trim().to_lowercase().as_str() {
        "x0" => Some(RegisterARM64::X0), "x1" => Some(RegisterARM64::X1), "x2" => Some(RegisterARM64::X2), "x3" => Some(RegisterARM64::X3),
        "x4" => Some(RegisterARM64::X4), "x5" => Some(RegisterARM64::X5), "x6" => Some(RegisterARM64::X6), "x7" => Some(RegisterARM64::X7),
        "x8" => Some(RegisterARM64::X8), "x9" => Some(RegisterARM64::X9), "x10" => Some(RegisterARM64::X10), "x11" => Some(RegisterARM64::X11),
        "x12" => Some(RegisterARM64::X12), "x13" => Some(RegisterARM64::X13), "x14" => Some(RegisterARM64::X14), "x15" => Some(RegisterARM64::X15),
        "x16" => Some(RegisterARM64::X16), "x17" => Some(RegisterARM64::X17), "x18" => Some(RegisterARM64::X18), "x19" => Some(RegisterARM64::X19),
        "x20" => Some(RegisterARM64::X20), "x21" => Some(RegisterARM64::X21), "x22" => Some(RegisterARM64::X22), "x23" => Some(RegisterARM64::X23),
        "x24" => Some(RegisterARM64::X24), "x25" => Some(RegisterARM64::X25), "x26" => Some(RegisterARM64::X26), "x27" => Some(RegisterARM64::X27),
        "x28" => Some(RegisterARM64::X28), "x29" => Some(RegisterARM64::X29), "x30" => Some(RegisterARM64::X30), _ => None,
    }
}

fn parse_sysreg(s: &str) -> SysReg {
    if s.contains("vbar_el") { SysReg::VbarEl1 } else if s.contains("elr_el1") { SysReg::ElrEl1 } else if s.contains("spsr_el1") { SysReg::SpsrEl1 }
    else if s.contains("sp_el0") { SysReg::SpEl0 } else if s.contains("fpcr") { SysReg::Fpcr } else if s.contains("fpsr") { SysReg::Fpsr }
    else if s.contains("tpidr_el1") { SysReg::TpidrEl1 } else if s.contains("tpidr_el0") { SysReg::TpidrEl0 } else if s.contains("tpidrro_el0") { SysReg::TpidrroEl0 }
    else if s.contains("cntv_cval") { SysReg::CntvCval } else if s.contains("cntp_cval") { SysReg::CntpCval } else if s.contains("cntv_tval") { SysReg::CntvTval }
    else if s.contains("cntp_tval") { SysReg::CntpTval } else if s.contains("cntv_ctl") { SysReg::CntvCtl } else if s.contains("cntp_ctl") { SysReg::CntpCtl }
    else if s.contains("daif") { SysReg::Daif } else if s.contains("cpacr_el1") { SysReg::CpacrEl1 } else if s.contains("sctlr_el1") { SysReg::SctlrEl1 }
    else if s.contains("tcr_el1") { SysReg::TcrEl1 } else if s.contains("cntpct") { SysReg::Cntpct } else if s.contains("cntvct") { SysReg::Cntvct }
    else if s.contains("currentel") { SysReg::CurrentEl } else if s.contains("cntfrq") { SysReg::Cntfrq } else if s.contains("esr_el1") { SysReg::EsrEl1 }
    else if s.contains("far_el1") { SysReg::FarEl1 } else if s.contains("dczid_el0") { SysReg::DczidEl0 } else if s.contains("midr") { SysReg::Midr }
    else { SysReg::Unknown }
}

fn check_and_fire_interrupts(uc: &mut Unicorn<EmuState>, pc: u64) -> bool {
    let nzcv = uc.reg_read(RegisterARM64::NZCV).unwrap_or(0);
    
    {
        let state = uc.get_data_mut();
        while let Ok(b) = state.rx_receiver.try_recv() { state.rx_fifo.push_back(b); }
    }

    let (vbar_el1, daif, has_uart_int, uart_irq_num, cnt_pending, irq_30, irq_27) = {
        let state = uc.get_data();
        let current_ticks = state.insn_count * TIME_WARP_MULTIPLIER;
        let mut enabled_uart = -1;
        for irq in 32..=35 { if state.interrupts_enabled.contains(&irq) { enabled_uart = irq as i32; break; } }
        let rx_int = !state.rx_fifo.is_empty() && ((state.uart_ier & 0x01) != 0);
        let tx_int = state.tx_irq_pending && ((state.uart_ier & 0x02) != 0);
        let uart_int = enabled_uart != -1 && (rx_int || tx_int);
        let cnt_int = (state.cntv_ctl & 1 != 0) && (state.cntv_ctl & 2 == 0) && current_ticks >= state.cntv_cval;
        (state.vbar_el1, state.pstate_daif, uart_int, enabled_uart, cnt_int, state.interrupts_enabled.contains(&30), state.interrupts_enabled.contains(&27))
    };

    if vbar_el1 == 0 || (daif & 0x80) != 0 { return false; }
    
    let mut fire_irq = -1;
    if has_uart_int { fire_irq = uart_irq_num; } else if cnt_pending { fire_irq = if irq_30 { 30 } else if irq_27 { 27 } else { 30 }; }

    if fire_irq != -1 {
        let state = uc.get_data_mut();
        state.active_irq = fire_irq;
        state.timer_pending = true;
        state.spsr_el1 = nzcv | state.pstate_daif | 0x05;
        state.elr_el1 = pc;
        state.pstate_daif |= 0x80;
        let target = state.vbar_el1 + 0x280;
        uc.reg_write(RegisterARM64::PC, target).unwrap();
        uc.emu_stop().unwrap();
        return true;
    }
    false
}

fn main() {
    println!("🚀 Запуск эмулятора PinePhone. Поднимаем NuttX...");
    let _ = Command::new("sh").arg("-c").arg("stty raw -echo < /dev/tty").status();
    
    ctrlc::set_handler(move || {
        let _ = Command::new("sh").arg("-c").arg("stty sane < /dev/tty").status();
        std::process::exit(0);
    }).unwrap();

    let (tx, rx) = mpsc::channel();
    let tx_sfml = tx.clone(); 

    thread::spawn(move || {
        let mut buffer = [0u8; 1];
        let mut stdin = io::stdin();
        loop {
            if let Ok(1) = stdin.read(&mut buffer) {
                let mut b = buffer[0];
                if b == 0x03 {
                    let _ = Command::new("sh").arg("-c").arg("stty sane < /dev/tty").status();
                    println!("\n\r[!] Эмулятор остановлен пользователем.");
                    std::process::exit(0);
                }
                if b == b'\n' { b = b'\r'; } 
                let _ = tx.send(b);
            }
        }
    });

    let framebuffer_shared = Arc::new(Mutex::new(vec![0u8; FB_SIZE]));
    let fb_clone = Arc::clone(&framebuffer_shared);
    
    // Общее состояние светодиодов
    let hardware_leds = Arc::new(Mutex::new(0u32));
    let leds_clone = Arc::clone(&hardware_leds);

    thread::spawn(move || {
        let file = File::create(LOG_FILE).expect("Не удалось создать log.txt");
        let log_filter = Arc::new(Mutex::new(LogFilter::new(file)));

        let elf_data = fs::read(ELF_FILE).expect("Файл nuttx_elf не найден!");
        let elf_file = object::File::parse(&*elf_data).expect("Ошибка парсинга ELF");

        let mut unicorn = Unicorn::new_with_data(Arch::ARM64, Mode::LITTLE_ENDIAN, EmuState::new(rx, log_filter.clone())).unwrap();
        unicorn.mem_map(0x00000000, 2 * 1024 * 1024 * 1024, Prot::ALL).unwrap();

        for sym in elf_file.symbols() {
            if let Ok(name) = sym.name() {
                let addr = sym.address();
                if addr > 0 && ["up_ndelay", "up_udelay", "up_mdelay", "arm64_udelay", "arm64_mdelay"].contains(&name) {
                    unicorn.get_data_mut().skip_functions.insert(addr);
                }
            }
        }

        for seg in elf_file.segments() {
            if let Ok(data) = seg.data() { if !data.is_empty() { unicorn.mem_write(seg.address(), data).unwrap(); } }
        }

        let entry_point = elf_file.entry();
        let bootstrap_addr = 0x1000;
        let bootstrap_code: [u8; 24] = [
            0x80, 0x00, 0x00, 0x58, 0x00, 0x10, 0x18, 0xd5, 0x20, 0x00, 0x1f, 0xd6,
            0x1f, 0x20, 0x03, 0xd5, 0x00, 0x00, 0x30, 0x00, 0x00, 0x00, 0x00, 0x00,
        ];
        let mut bootstrap_code_full = bootstrap_code;
        bootstrap_code_full[16..24].copy_from_slice(&entry_point.to_le_bytes());
        unicorn.mem_write(bootstrap_addr, &bootstrap_code_full).unwrap();
        unicorn.reg_write(RegisterARM64::X1, entry_point).unwrap();
        unicorn.reg_write(RegisterARM64::SP, 0x48000000).unwrap(); 

        let cs = Arc::new(Capstone::new().arm64().mode(ArchMode::Arm).endian(Endian::Little).detail(true).build().unwrap());
        let cs_clone = Arc::clone(&cs);

        unicorn.add_code_hook(1, 0, move |uc, address, _size| {
            uc.get_data_mut().insn_count += 1;

            if uc.get_data().skip_functions.contains(&address) {
                let lr = uc.reg_read(RegisterARM64::X30).unwrap();
                uc.get_data_mut().insn_count += 50_000;
                uc.reg_write(RegisterARM64::PC, lr).unwrap();
                uc.emu_stop().unwrap();
                return;
            }

            if uc.get_data().insn_count % 5000 == 0 {
                if check_and_fire_interrupts(uc, address) { return; }
            }

            let mut inst_bytes = [0u8; 4];
            if uc.mem_read(address, &mut inst_bytes).is_err() { return; }
            let top = inst_bytes[3];
            if top != 0xD4 && top != 0xD5 && top != 0xD6 && top != 0x7F { return; }

            let inst = u32::from_le_bytes(inst_bytes);
            
            if inst_bytes == [0x1f, 0x20, 0x03, 0xd5] || inst_bytes == [0xdf, 0x03, 0x20, 0x7f] || inst_bytes == [0x7f, 0x20, 0x03, 0xd5] || inst_bytes == [0x5f, 0x20, 0x03, 0xd5] {
                uc.get_data_mut().insn_count += 50_000;
                uc.reg_write(RegisterARM64::PC, address + 4).unwrap();
                uc.emu_stop().unwrap();
                return;
            }
            if inst_bytes == [0xe0, 0x03, 0x9f, 0xd6] { 
                let (target_pc, spsr) = { 
                    let state = uc.get_data_mut(); 
                    state.timer_pending = false; 
                    state.pstate_daif = state.spsr_el1 & 0x3C0; 
                    (state.elr_el1, state.spsr_el1) 
                };
                uc.reg_write(RegisterARM64::NZCV, spsr & 0xF0000000).unwrap();
                uc.reg_write(RegisterARM64::PC, target_pc).unwrap();
                uc.emu_stop().unwrap();
                return;
            }

            let is_svc = (inst & 0xFFE0001F) == 0xD4000001;
            let is_smc = (inst & 0xFFE0001F) == 0xD4000003;

            if is_svc {
                let nzcv = uc.reg_read(RegisterARM64::NZCV).unwrap_or(0);
                let state = uc.get_data_mut();
                state.esr_el1 = 0x56000000;
                if state.vbar_el1 != 0 {
                    let from_el1 = (state.pstate_daif & 0x0F) != 0;
                    state.spsr_el1 = nzcv | state.pstate_daif | (if from_el1 { 0x05 } else { 0x00 });
                    state.pstate_daif |= 0x3C0;
                    state.elr_el1 = address + 4;
                    let target_pc = state.vbar_el1 + if from_el1 { 0x200 } else { 0x400 };
                    uc.reg_write(RegisterARM64::PC, target_pc).unwrap();
                    uc.emu_stop().unwrap();
                }
                return;
            }
            if is_smc {
                let x0 = uc.reg_read(RegisterARM64::X0).unwrap_or(0);
                uc.reg_write(RegisterARM64::X0, if x0 == 0x84000000 { 2 } else { -1i64 as u64 }).unwrap();
                uc.reg_write(RegisterARM64::PC, address + 4).unwrap();
                uc.emu_stop().unwrap();
                return;
            }

            if top == 0xD5 {
                let mut action = Action::Ignore;
                if let Some(&act) = uc.get_data().insn_cache.get(&inst) {
                    action = act;
                } else {
                    if let Ok(insns) = cs_clone.disasm_all(&inst_bytes, address) {
                        if let Some(i) = insns.iter().next() {
                            let mnem = i.mnemonic().unwrap_or("");
                            let op_str = i.op_str().unwrap_or("").to_lowercase();
                            let parts: Vec<&str> = op_str.split(',').map(|s| s.trim()).collect();
                            
                            if mnem == "msr" && parts.len() == 2 {
                                if op_str.contains("daifset") {
                                    let imm = u64::from_str_radix(parts[1].trim_start_matches('#').trim_start_matches("0x"), 16).unwrap_or(0);
                                    action = Action::DaifSet(imm);
                                } else if op_str.contains("daifclr") {
                                    let imm = u64::from_str_radix(parts[1].trim_start_matches('#').trim_start_matches("0x"), 16).unwrap_or(0);
                                    action = Action::DaifClr(imm);
                                } else if let Some(src_reg) = parse_reg(parts[1]) {
                                    action = Action::Msr(src_reg, parse_sysreg(parts[0]));
                                }
                            } else if mnem == "mrs" && parts.len() == 2 {
                                if let Some(dest_reg) = parse_reg(parts[0]) {
                                    action = Action::Mrs(dest_reg, parse_sysreg(parts[1]));
                                }
                            } else if mnem == "dc" && parts.len() == 2 && parts[0] == "zva" {
                                if let Some(target_reg) = parse_reg(parts[1]) {
                                    action = Action::DcZva(target_reg);
                                }
                            }
                        }
                    }
                    uc.get_data_mut().insn_cache.insert(inst, action);
                }

                match action {
                    Action::DaifSet(imm) => { uc.get_data_mut().pstate_daif |= imm << 6; uc.reg_write(RegisterARM64::PC, address + 4).unwrap(); uc.emu_stop().unwrap(); },
                    Action::DaifClr(imm) => { uc.get_data_mut().pstate_daif &= !(imm << 6); uc.reg_write(RegisterARM64::PC, address + 4).unwrap(); uc.emu_stop().unwrap(); },
                    Action::DcZva(reg) => { let addr = uc.reg_read(reg).unwrap(); let _ = uc.mem_write(addr, &[0u8; 64]); uc.reg_write(RegisterARM64::PC, address + 4).unwrap(); uc.emu_stop().unwrap(); },
                    Action::Msr(reg, sys) => {
                        let val = uc.reg_read(reg).unwrap();
                        let st = uc.get_data_mut();
                        let ticks = st.insn_count * TIME_WARP_MULTIPLIER;
                        match sys {
                            SysReg::VbarEl1 => st.vbar_el1 = val, SysReg::ElrEl1 => st.elr_el1 = val, SysReg::SpsrEl1 => st.spsr_el1 = val, SysReg::SpEl0 => st.sp_el0 = val,
                            SysReg::Fpcr => st.fpcr = val, SysReg::Fpsr => st.fpsr = val, SysReg::TpidrEl1 => st.tpidr_el1 = val, SysReg::TpidrEl0 => st.tpidr_el0 = val,
                            SysReg::TpidrroEl0 => st.tpidrro_el0 = val, SysReg::CntvCval | SysReg::CntpCval => st.cntv_cval = val,
                            SysReg::CntvTval | SysReg::CntpTval => st.cntv_cval = ticks + (val as i32 as u64), SysReg::CntvCtl | SysReg::CntpCtl => st.cntv_ctl = val,
                            SysReg::Daif => st.pstate_daif = val, SysReg::CpacrEl1 => st.cpacr_el1 = val, SysReg::SctlrEl1 => st.sctlr_el1 = val, SysReg::TcrEl1 => st.tcr_el1 = val, _ => {}
                        }
                        uc.reg_write(RegisterARM64::PC, address + 4).unwrap(); uc.emu_stop().unwrap();
                    },
                    Action::Mrs(reg, sys) => {
                        let st = uc.get_data();
                        let ticks = st.insn_count * TIME_WARP_MULTIPLIER;
                        let val = match sys {
                            SysReg::Cntpct | SysReg::Cntvct => ticks, SysReg::CurrentEl => 4, SysReg::VbarEl1 => st.vbar_el1, SysReg::ElrEl1 => st.elr_el1, SysReg::SpsrEl1 => st.spsr_el1,
                            SysReg::SpEl0 => st.sp_el0, SysReg::Fpcr => st.fpcr, SysReg::Fpsr => st.fpsr, SysReg::Daif => st.pstate_daif, SysReg::TpidrEl1 => st.tpidr_el1,
                            SysReg::TpidrEl0 => st.tpidr_el0, SysReg::TpidrroEl0 => st.tpidrro_el0, SysReg::CntpCtl | SysReg::CntvCtl => st.cntv_ctl,
                            SysReg::CntpCval | SysReg::CntvCval => st.cntv_cval, SysReg::CntpTval | SysReg::CntvTval => st.cntv_cval.saturating_sub(ticks),
                            SysReg::Cntfrq => 24_000_000, SysReg::CpacrEl1 => st.cpacr_el1, SysReg::SctlrEl1 => st.sctlr_el1, SysReg::TcrEl1 => st.tcr_el1,
                            SysReg::EsrEl1 => st.esr_el1, SysReg::FarEl1 => st.far_el1, SysReg::DczidEl0 => 4, SysReg::Midr => 0x410FC080, _ => 0,
                        };
                        uc.reg_write(reg, val).unwrap(); uc.reg_write(RegisterARM64::PC, address + 4).unwrap(); uc.emu_stop().unwrap();
                    },
                    Action::Ignore => {}
                }
            }
        }).unwrap();

        // ХУК ДЛЯ НАШИХ СВЕТОДИОДОВ (Ловим запись по аппаратному адресу 0x02000000)
        unicorn.add_mem_hook(HookType::MEM_WRITE, LED_BASE, LED_BASE + 4, move |_, _, address, _, value| {
            if address == LED_BASE {
                if let Ok(mut leds) = leds_clone.try_lock() {
                    *leds = value as u32;
                }
            }
            true
        }).unwrap();

        unicorn.add_mem_hook(HookType::MEM_WRITE, UART0_BASE, UART0_BASE + UART_RANGE, move |uc, _, address, _, value| {
            let val8 = (value & 0xFF) as u8; let st = uc.get_data_mut(); let offset = address & 0x3FF;
            if offset == 0x00 {
                if (st.uart_lcr & 0x80) != 0 { st.uart_dll = val8; } 
                else { 
                    let c = val8 as char;
                    if c == '\n' { print!("\r\n"); } else { print!("{}", c); }
                    io::stdout().flush().unwrap();
                    if (st.uart_ier & 0x02) != 0 { st.tx_irq_pending = true; }
                }
            } else if offset == 0x04 {
                if (st.uart_lcr & 0x80) != 0 { st.uart_dlh = val8; } 
                else { let old_ier = st.uart_ier; st.uart_ier = val8; if (old_ier & 0x02) == 0 && (val8 & 0x02) != 0 { st.tx_irq_pending = true; } }
            } else if offset == 0x0C { st.uart_lcr = val8; }
            true
        }).unwrap();

        unicorn.add_mem_hook(HookType::MEM_READ, UART0_BASE, UART0_BASE + UART_RANGE, move |uc, _, address, size, _| {
            let offset = address & 0x3FF;
            let (val, is_rbr) = {
                let st = uc.get_data_mut();
                match offset {
                    0x00 => if (st.uart_lcr & 0x80) != 0 { (st.uart_dll as u64, false) } else { (0, true) },
                    0x04 => if (st.uart_lcr & 0x80) != 0 { (st.uart_dlh as u64, false) } else { (st.uart_ier as u64, false) },
                    0x08 => { 
                        let rx_int = !st.rx_fifo.is_empty() && ((st.uart_ier & 0x01) != 0);
                        let iir = if rx_int { 0x04 } else if st.tx_irq_pending { st.tx_irq_pending = false; 0x02 } else { 0x01 };
                        (iir as u64, false)
                    },
                    0x0C => (st.uart_lcr as u64, false), 0x14 => { let has_data = !st.rx_fifo.is_empty(); (0x60 | (if has_data { 0x01 } else { 0x00 }), false) },
                    0x7C => (0x06, false), _ => (0, false),
                }
            };
            if is_rbr { let byte = uc.get_data_mut().rx_fifo.pop_front().unwrap_or(0); let mut val_bytes = [0u8; 8]; val_bytes[0] = byte; uc.mem_write(address, &val_bytes[0..size]).unwrap(); } 
            else { uc.mem_write(address, &val.to_le_bytes()[0..size]).unwrap(); }
            true
        }).unwrap();

        unicorn.add_mem_hook(HookType::MEM_WRITE, GICD_BASE, GICD_BASE + 0x1000, move |uc, _, address, _, value| {
            let state = uc.get_data_mut();
            if address == GICC_CTLR { state.gic_enabled = (value & 0x1) != 0; return true; }
            if address >= GICD_ISENABLER && address < GICD_ISENABLER + 0x80 { let irq_base = ((address - GICD_ISENABLER) / 4) as u32 * 32; for bit in 0..32 { if value & (1 << bit) != 0 { state.interrupts_enabled.insert(irq_base + bit); } } }
            if address == GIC_EOIR { state.timer_pending = false; }
            true
        }).unwrap();

        unicorn.add_mem_hook(HookType::MEM_READ, GICC_BASE, GICC_BASE + 0x1000, move |uc, _, address, size, _| {
            let val = if address == GIC_IAR || address == GICC_HPPIR { let state = uc.get_data_mut(); if state.timer_pending { state.timer_pending = false; state.active_irq as u64 } else { 1023 } } else if address == GICC_RPR { 0xFF } else { 0 };
            uc.mem_write(address, &val.to_le_bytes()[0..size]).unwrap();
            true
        }).unwrap();

        unicorn.add_mem_hook(HookType::MEM_WRITE, MMIO_BASE, MMIO_BASE + MMIO_SIZE, move |uc, _, address, _, value| {
            if (address >= UART0_BASE && address < UART0_BASE + UART_RANGE) || (address >= GICD_BASE && address < GICD_BASE + 0x1000) || (address >= GICC_BASE && address < GICC_BASE + 0x1000) { return true; }
            uc.get_data_mut().mmio_state.insert(address, value as u32); uc.get_data_mut().mmio_reads.insert(address, 0); true
        }).unwrap();

        unicorn.add_mem_hook(HookType::MEM_READ, MMIO_BASE, MMIO_BASE + MMIO_SIZE, move |uc, _, address, size, _| {
            if (address >= UART0_BASE && address < UART0_BASE + UART_RANGE) || (address >= GICD_BASE && address < GICD_BASE + 0x1000) || (address >= GICC_BASE && address < GICC_BASE + 0x1000) { return true; }
            let val = { let state = uc.get_data_mut(); let val = *state.mmio_state.get(&address).unwrap_or(&0); let count = state.mmio_reads.entry(address).or_insert(0); *count += 1; if *count > 100 { 0 } else if *count > 50 { 0xFFFF_FFFF } else { val as u64 } };
            uc.mem_write(address, &val.to_le_bytes()[0..size]).unwrap(); true
        }).unwrap();

        let mut current_pc = bootstrap_addr;
        let mut last_screen_sync = 0;
        
        loop {
            if unicorn.get_data().insn_count > MAX_INSN_LIMIT { break; }
            
            match unicorn.emu_start(current_pc, NEVER_REACH_ADDR, 0, 50_000) {
                Ok(_) => {
                    current_pc = unicorn.reg_read(RegisterARM64::PC).unwrap();
                    if current_pc == NEVER_REACH_ADDR { break; }
                    
                    let insns = unicorn.get_data().insn_count;
                    if insns > last_screen_sync + 150_000 {
                        last_screen_sync = insns;
                        if let Ok(mut fb) = fb_clone.try_lock() {
                            let _ = unicorn.mem_read(FB_BASE, &mut fb);
                        }
                    }
                }
                Err(e) => {
                    let pc = unicorn.reg_read(RegisterARM64::PC).unwrap_or(0);
                    println!("\n\r\n\r[!] ОШИБКА ЭМУЛЯЦИИ: {:?} на PC = {:#018X}", e, pc);
                    let _ = Command::new("sh").arg("-c").arg("stty sane < /dev/tty").status();
                    break;
                }
            }
        }
        let _ = Command::new("sh").arg("-c").arg("stty sane < /dev/tty").status();
    });

    let mut window = RenderWindow::new(
        (WINDOW_WIDTH, WINDOW_HEIGHT), // Окно стало выше (290px вместо 240px)
        "PinePhone (NuttX) + LEDs",
        Style::CLOSE | Style::TITLEBAR,
        &Default::default(),
    );
    window.set_framerate_limit(60);

    let mut texture = Texture::new().expect("Не удалось создать текстуру");
    if !texture.create(FB_WIDTH as u32, FB_HEIGHT as u32) {
        panic!("Не удалось задать размер текстуры");
    }

    let mut last_render = Instant::now();

    while window.is_open() {
        while let Some(event) = window.poll_event() {
            match event {
                Event::Closed => {
                    let _ = Command::new("sh").arg("-c").arg("stty sane < /dev/tty").status();
                    window.close();
                    std::process::exit(0);
                }
                Event::TextEntered { unicode } => {
                    let mut b = unicode as u8;
                    if b == b'\n' || b == 13 { b = b'\r'; }
                    let _ = tx_sfml.send(b);
                }
                _ => {}
            }
        }

        if last_render.elapsed().as_millis() >= 33 {
            last_render = Instant::now();
            if let Ok(pixels) = framebuffer_shared.try_lock() {
                unsafe {
                    texture.update_from_pixels(&pixels, FB_WIDTH as u32, FB_HEIGHT as u32, 0, 0);
                }
            }
        }

        window.clear(Color::rgb(20, 20, 20)); // Темно-серый фон окна

        // 1. Отрисовываем Экран
        let sprite = Sprite::with_texture(&texture);
        window.draw(&sprite);

        // 2. Отрисовываем нижнюю панель "Платы"
        let mut board_rect = RectangleShape::new();
        board_rect.set_size((WINDOW_WIDTH as f32, 50.0));
        board_rect.set_position((0.0, FB_HEIGHT as f32));
        board_rect.set_fill_color(Color::rgb(30, 40, 30)); // Цвет текстолита
        window.draw(&board_rect);

        // 3. Рисуем 4 аппаратных светодиода
        let leds_val = *hardware_leds.lock().unwrap();
        
        let colors = [
            (Color::rgb(255, 0, 0), Color::rgb(50, 0, 0)),     // LED 1: Красный
            (Color::rgb(0, 255, 0), Color::rgb(0, 50, 0)),     // LED 2: Зеленый
            (Color::rgb(255, 255, 0), Color::rgb(50, 50, 0)),  // LED 3: Желтый
            (Color::rgb(0, 100, 255), Color::rgb(0, 0, 50)),   // LED 4: Синий
        ];

        for i in 0..4 {
            let mut led = CircleShape::new(8.0, 30);
            led.set_position((40.0 + (i as f32) * 40.0, FB_HEIGHT as f32 + 15.0));
            
            let is_on = (leds_val & (1 << i)) != 0;
            led.set_fill_color(if is_on { colors[i].0 } else { colors[i].1 });
            
            // Если горит - добавляем обводку (ореол)
            if is_on {
                led.set_outline_thickness(2.0);
                led.set_outline_color(Color::rgb(255, 255, 255));
            }
            
            window.draw(&led);
        }

        window.display();
    }
}