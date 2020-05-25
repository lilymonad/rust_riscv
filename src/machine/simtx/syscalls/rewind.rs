{
    let _cid = self.warps[wid].get_single_core_id();
    let core = &mut self.warps[wid].cores[wid];
    let mut addr = core.registers[10] as usize;
    let size = core.registers[11] as usize;
    let fp = core.registers[12];

    match fp {
        0 | 1 | 2 => panic!("reading from stdout or stderr"),
        n => {
            self.file_handles.get_mut(&n).map(|file| {
                let _ = file.seek(SeekFrom::Start(0))
                    .map_err(|_| {
                        println!("LOL")
                    });
            });
        },
    }

    self.warps[wid].advance_pc(pathid, advance);
}
