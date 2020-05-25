{
    for i in self.warps[wid].alive_cores_ids() {
        let ptr = self.warps[wid].cores[i].registers[10];
        self.free(ptr as usize);
    }
    self.warps[wid].advance_pc(pathid, advance);
}
