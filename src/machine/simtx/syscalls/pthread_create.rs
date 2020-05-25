{
assert!(self.warps[wid].paths[pathid].is_single(),
"pthread_create must be called by only 1 thread");

// allocate a new thread (get its id)
let tid = self.pop_first_idle();
let w = tid / tpw; let t = tid % tpw;

let stacksize = self.stack_size;
let stackstart = self.stack_start - stacksize * tid; 
let stackend = stackstart - stacksize;
mem.allocate_at(stackend, stacksize);

let cid = self.warps[wid].get_single_core_id();
// write in memory the tid
let addr = self.warps[wid].cores[cid].registers[10] as usize;
mem.set_32(addr, tid as u32);

// setup allocated core's register file
let mut regs = [0;32];
regs[2] = stackstart as i32;
regs[8] = stackstart as i32;
regs[3] = self.warps[wid].cores[cid].registers[3];
regs[4] = tid as i32;
regs[10] = self.warps[wid].cores[cid].registers[13];
self.warps[w].cores[t].registers = regs;

// setup a new path with only allocated thread inside
let npc = self.warps[wid].cores[cid].registers[12];
let m = BitSet::singleton(t);

self.warps[w].push_path(Path::from_pc_mask(npc, m));

// return 0 and advance current path
self.warps[wid].cores[cid].set_ri(10, 0);
self.warps[wid].advance_pc(pathid, advance);
}
