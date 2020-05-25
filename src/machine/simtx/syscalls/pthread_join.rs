{
let cid = self.warps[wid].get_single_core_id();
let to_wait = self.warps[wid].cores[cid].registers[10] as usize;
if self.idle_threads.contains(&to_wait) {
    self.warps[wid].advance_pc(pathid, advance);
}
}
