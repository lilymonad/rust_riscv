use std::collections::HashMap;
use memory::Memory;

/// Use the function to load code (`.text` section) into a memory buffer.
pub fn load_instructions(file:&elflib::File, mem:&mut dyn Memory) -> bool {
    file.get_section(".text").map_or(false, | text | -> bool {
        let mut i = 0;
        while i < text.data.len() {
            let x = if file.ehdr.data == elflib::types::ELFDATA2LSB {
                u32::from_be(text.data.get_32(i))
            } else {
                u32::from_le(text.data.get_32(i))
            };

            let addr = (text.shdr.addr as usize) + i;
            mem.set_32(addr, x);

            i += 4
        }

        true
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
