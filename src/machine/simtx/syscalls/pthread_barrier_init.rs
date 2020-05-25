{
let cid = self.warps[wid].get_single_core_id();
let num = self.warps[wid].cores[cid].registers[12];
let ptr = self.warps[wid].cores[cid].registers[10];

self.barriers.insert(ptr, Barrier {
    initial_cap:num,
    current_cap:num,
});

self.warps[wid].advance_pc(pathid, advance);
}
