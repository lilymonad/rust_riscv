{
    for i in self.warps[wid].alive_cores_ids() {
        let size = self.warps[wid].cores[i].registers[10];
        let ptr = self.malloc(mem.deref_mut(), size as usize);
        self.warps[wid].cores[i].set_ri(10, ptr as i32);
        #[cfg(debug_assertions)]
        println!("MALLOC CALLED ADRESSE EST {:x}", ptr);
    }
    self.warps[wid].advance_pc(pathid, advance);
}
