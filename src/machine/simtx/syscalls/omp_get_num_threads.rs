{
    for i in self.warps[wid].alive_cores_ids() {
        let num_warps = self.warps.len();
        let core = &mut self.warps[wid].cores[i];
        core.set_ri(10, (num_warps * tpw) as i32);
    }
    self.warps[wid].advance_pc(pathid, advance);
}
