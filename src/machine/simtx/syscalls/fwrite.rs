{
    for i in self.warps[wid].alive_cores_ids() {
        let core = &mut self.warps[wid].cores[i];
        let file_desc = core.registers[13];
        let mut str_addr = core.registers[10];
        let mut to_write = String::new();
        let mut byte = mem.get_8(str_addr as usize);
        while byte != 0 {
            to_write.push(byte as char);
            str_addr += 1;
            byte = mem.get_8(str_addr as usize);
        }
        match file_desc {
            0 => print!("{}", to_write),
            1 => panic!("writing to stdin"),
            2 => eprint!("{}", to_write),
            n => self.file_handles.get_mut(&n).map(|f| {
                match f.write(to_write.as_bytes()) {
                    Err(_) => {},
                    Ok(_size) => {},
                }
            }).expect("[SIM] Cannot open file"),
        };
    }
    self.warps[wid].advance_pc(pathid, advance);
}
