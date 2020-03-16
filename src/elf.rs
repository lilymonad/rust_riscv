use std::{
    collections::HashMap,
//    env,
//    path::Path,
};
use memory::{Memory, /*Storable*/};

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
    load_section_with_offset(file, section, mem, 0)
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
    get_symbol_address(file, "main")
}

/// Use this function to retrieve the address of any symbol in the elf.
/// Return `None` if the symbol is not present.
pub fn get_symbol_address(file:&elflib::File, symbol:&str) -> Option<i32> {
    let symtab = file.get_section(".symtab")?;
    let symbols = file.get_symbols(symtab).ok()?;

    for sym in symbols {
        if sym.name == symbol {
            return Some(sym.value as i32)
        }
    }

    None
}

/// Use this function to load a while `.elf` file in memory. Every needed
/// sections are loaded in memory.
pub fn load_program(file:&elflib::File, mem:&mut dyn Memory) -> Option<(usize, usize)> {
    load_program_with_offset(file, mem, 0)
}
/*
#[derive(Debug)]
pub struct Elf32Dyn {
    d_tag:i32,
    d_un:u32,
}

impl Storable for Elf32Dyn {
    fn read_from(mem:&dyn Memory, addr:usize) -> Self {
        let d_tag = mem.get_32(addr) as i32;
        let d_un = mem.get_32(addr + 4);
        Elf32Dyn { d_tag, d_un }
    }

    fn store_to(&self, mem:&mut dyn Memory, addr:usize) {
        mem.set_32(addr, self.d_tag as u32);
        mem.set_32(addr + 4, self.d_un)
    }
}

impl Storable for String {
    fn read_from(mem:&dyn Memory, addr:usize) -> Self {
        let mut ret = String::new();
        let mut i = addr;
        let mut c = mem.get_8(i);

        while c != 0 {
            ret.push(c as char);
            i += 1;
            c = mem.get_8(i);
        }

        ret
    }

    fn store_to(&self, mem:&mut dyn Memory, addr:usize) {
        let mut i = addr;
        for c in self.chars() {
            mem.set_8(i, c as u8);
            i += 1;
        }
        mem.set_8(i, 0);
    }
}

struct LibInfo {
    mem_offset:usize,
    symbols_offsets:HashMap<String, usize>,
}

struct DependencyGraph {
    next_usable_addr:usize,
    libinfos:HashMap<String, LibInfo>,
}

pub fn load_dependencies(file:&elflib::File, mem:&mut dyn Memory) -> Option<()> {
    load_deps_rec(file, mem, &mut DependencyGraph { next_usable_addr:0x7FFFFFFF, libinfos:HashMap::new() })
}

fn load_deps_rec(
      file:&elflib::File
    , mem:&mut dyn Memory
    , data:&mut DependencyGraph)
-> Option<()> {

    if let  Some(dynamic) = file.get_section(".dynamic") {
        let dynstrs = &(file.get_section(".dynstr")?).data;
        let step = dynamic.shdr.entsize as usize;
        let size = dynamic.shdr.size as usize;
        for i in (0..size).step_by(step) {
            let entry = Elf32Dyn::read_from(&dynamic.data, i);

            // if the dynamic entry represent a needed shared lib
            if entry.d_tag == 1 {
                // get its name
                let off = entry.d_un as usize;
                let dep_name = String::read_from(dynstrs, off);

                // search for the lib's entry, load it if necessary
                let info = data.libinfos.entry(dep_name)
                    .or_insert(load_dyn_lib(dep_name, mem, &mut data)?);

                // update the .got section of the current binary
                update_got(file, mem, info)?;
            }
        }
    }
    Some(())
}

fn update_got(file:&elflib::File, mem:&mut dyn Memory, info:&LibInfo) -> Option<()> {
    let dynsym = file.get_section(".dynsym")?;
    let symbols = file.get_symbols(dynsym).ok()?;
    let got_off = file.get_section(".got").map(|s| s.shdr.addr as usize)?;

    for sym in symbols {

    }

    Some(())
}

fn load_dyn_lib(s:String, mem:&mut dyn Memory, data:&mut DependencyGraph) -> Option<LibInfo> {

    // search for the file
    let dirs = env::var("PATH").ok()?;

    let mut file : Option<elflib::File> = None;
    for d in dirs.split(":").map(Path::new) {
        let full = d.join(&s);
        if let Ok(f) = elflib::File::open_path(&full) {
            file = Some(f)
        }
    }

    // file found, load it into memory
    let file = file?;
    let (beg, end) = load_program_with_offset(&file, mem, data.next_usable_addr)?;

    // load its dependencies, starting from the end of this lib
    data.next_usable_addr = end + 1;
    load_deps_rec(&file, mem, data)?;

    // compute its infos
    let mem_offset = beg;
    let mut symbols_offsets = HashMap::new();

    let symtab = file.get_section(".symtab")?;
    let symbols = file.get_symbols(symtab).ok()?;
    for sym in symbols {
        if sym.bind != elflib::types::STB_LOCAL {
             symbols_offsets.insert(sym.name, sym.value as usize);
        }
    }

    Some(LibInfo { mem_offset, symbols_offsets })
}*/

fn load_program_with_offset(file:&elflib::File, mem:&mut dyn Memory, off:usize)
-> Option<(usize, usize)> {
    let mut beg : usize = 0;
    let mut end : usize = 0;
    for section in &file.sections {
        println!("loading section {} from {:x} to {:x}"
            , section.shdr.name
            , section.shdr.addr
            , section.shdr.addr + section.shdr.size);
        let addr = section.shdr.addr as usize;
        if addr == 0 { continue }

        let (a, b) = load_section_with_offset(file, section.shdr.name.as_str(), mem, off)?;
        beg = if beg == 0 || beg > a { a } else { beg };
        end = if end == 0 || end < b { b } else { end };
    }
    Some((beg, end))   
}

fn load_section_with_offset(file:&elflib::File, section:&str, mem:&mut dyn Memory, off:usize) -> Option<(usize, usize)> {
    file.get_section(section).and_then(| section | -> Option<(usize, usize)> {
        let mut rodata_i = off + section.shdr.addr as usize;

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
