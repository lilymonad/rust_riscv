{
    let _cid = self.warps[wid].get_single_core_id();
    let core = &mut self.warps[wid].cores[wid];
    let mut addr = core.registers[10] as usize;
    let mut c = mem.get_8(addr);
    let mut fname = String::new();
    while c != 0 {
        fname.push(c as char);
        addr += 1;
        c = mem.get_8(addr);
    }
    let mut oo = OpenOptions::new();
    oo
        .write(true)
        .read(true)
        .create(true);

    core.set_ri(10, match oo.open(&fname) {
        Err(_) => 0,
        Ok(f) => {
            self.file_handles.insert(self.next_fid
                , f);
            let ret = self.next_fid;
            self.next_fid += 1;
            ret
        },
    });

    self.warps[wid].advance_pc(pathid, advance);
}
