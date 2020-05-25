{
    for i in self.warps[wid].alive_cores_ids() {
        let core = &mut self.warps[wid].cores[i];
        let tid = wid*tpw + i;
        //println!("core {} omp_get_thread_num = {}", wid, tid);
        core.set_ri(10, tid as i32);
    }
    self.warps[wid].advance_pc(pathid, advance);
}
