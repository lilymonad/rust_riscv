{
for i in self.warps[wid].alive_cores_ids() {
    let core = &self.warps[wid].cores[i];
    let tid = wid*tpw + i;
    let ptr = core.registers[10];

    // don't re-execute the wait
    if self.in_barrier[tid] == ptr { continue }

    // if the barrier exists
    if let Some(barr) = self.barriers.get_mut(&ptr) {

        // put thread in barrier
        self.in_barrier[tid] = ptr;
        // decrement its capacity
        barr.current_cap -= 1;

        // it the barrier must open, free all threads
        // then stop the loop
        if barr.current_cap == 0 {
            barr.current_cap = barr.initial_cap;
            self.free_barrier(ptr, advance);
            break;
        }
    }
}
}
