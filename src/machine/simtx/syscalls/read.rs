{
    let _cid = self.warps[wid].get_single_core_id();
    let core = &mut self.warps[wid].cores[wid];
    let fp = core.registers[10];
    let mut addr = core.registers[11] as usize;
    let size = core.registers[12] as usize;

    match fp {
        0 | 2 => panic!("reading from stdout or stderr"),
        1 => {
            let mut buf = String::new();
            std::io::stdin().read_line(&mut buf).unwrap();
            for byte in buf.bytes() {
                mem.set_8(addr, byte);
                addr += 1;
            }
            mem.set_8(addr, 0);
        },
        n => {
            self.file_handles.get_mut(&n).map(|file| {
                let mut bytes = Read::by_ref(file).bytes();
                    let mut i = 0;
                    while i < size {
                        match bytes.next() {
                            Some(Ok(b)) => {
                                mem.set_8(addr + i, b);
                                if b as char == '\n' { break }
                            },
                            _ => break,
                        }
                        i += 1;
                    }
                    mem.set_8(addr + i, 0);
            });
        },
    }

    self.warps[wid].advance_pc(pathid, advance);
}
