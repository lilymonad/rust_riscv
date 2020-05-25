{
    let ids : Vec<usize> = self.warps[wid].alive_cores_ids().collect();
    if ids.len() != 1 { panic!("GOMP_parallel() called by more than one thread") }

    let id = ids[0];
    let core = &self.warps[wid].cores[id];
    let _function = core.registers[10];
}
