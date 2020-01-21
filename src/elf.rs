use std::collections::HashMap;
use memory::Memory;

/// Helper for `load_section(file, ".text", mem)`
pub fn load_instructions(file:&elflib::File, mem:&mut dyn Memory) -> Option<(usize, usize)> {
    load_section(file, ".text", mem)
}

/// Helper for `load_section(file, ".rodata", mem)`
pub fn load_rodata(file:&elflib::File, mem:&mut dyn Memory) -> Option<(usize, usize)> {
    load_section(file, ".rodata", mem)
}

/// Load a specific section from the file into the `mem` Memory. The section is
/// loaded at the memory offset specified in the file.
pub fn load_section(file:&elflib::File, section:&str, mem:&mut dyn Memory) -> Option<(usize, usize)> {
    file.get_section(section).map_or(None, | section | -> Option<(usize, usize)> {
        let mut rodata_i = section.shdr.addr as usize;

        mem.allocate_at(rodata_i, section.data.len());
        for byte in &section.data {
            mem.set_8(rodata_i, *byte);
            rodata_i += 1
        }

        let beg = section.shdr.addr as usize;
        let end = beg + section.data.len() as usize;
        Some((beg, end))
    })
}

/// Use this function to retrieve the mapping of linked functions addresses to
/// their name. Useful when emulating `libc` calls.
pub fn get_plt_symbols(file:&elflib::File) -> Option<HashMap<i32, String>> {
    let symtab = file.get_section(".symtab")?;
    let symbols = file.get_symbols(symtab).ok()?;
    let plt = file.get_section(".plt")?;
    let mut ret = HashMap::new();

    for sym in symbols {
        if sym.value >= plt.shdr.addr && sym.value < plt.shdr.addr + plt.shdr.size {
            ret.insert(sym.value as i32, sym.name);
        }
    }

    Some(ret)
}

/// Use this function to retrieve the address of a binary symbol in the elf.
pub fn get_main_pc(file:&elflib::File) -> Option<i32> {
    let symtab = file.get_section(".symtab")?;
    let symbols = file.get_symbols(symtab).ok()?;

    for sym in symbols {
        if sym.name == "main" {
            return Some(sym.value as i32)
        }
    }

    None
}

/// Use this function to retrieve the address of any symbol in the elf.
/// Return `None` if the symbol is not present.
pub fn get_symbol_address(file:&elflib::File, symbol:&str) -> Option<i32> {
    let symtab = file.get_section(".symtab")?;
    let symbols = file.get_symbols(symtab).ok()?;

    for sym in symbols {
        if sym.name.contains(symbol) {
            return Some(sym.value as i32)
        }
    }

    None
}

/// Use this function to load a while `.elf` file in memory. Every needed
/// sections are loaded in memory.
pub fn load_program(file:&elflib::File, mem:&mut dyn Memory) -> Option<(usize, usize)> {
    let mut beg : usize = 0;
    let mut end : usize = 0;
    for section in &file.sections {
        let addr = section.shdr.addr as usize;
        if addr == 0 { continue }

        let (a, b) = load_section(file, section.shdr.name.as_str(), mem)?;
        beg = if beg == 0 || beg > a { a } else { beg };
        end = if end == 0 || end < b { b } else { end };
    }
    Some((beg, end))
}
