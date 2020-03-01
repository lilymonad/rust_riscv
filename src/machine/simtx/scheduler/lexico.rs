use machine::simtx::{Warp, Path, scheduler::SimtxScheduler};

const SCHEDULE_THRESHOLD : usize = 256;
const RR_ROUNDS : usize = 256;

#[derive(Clone)]
pub struct Scheduler {
    cycles_until_rr:usize,
    rr_pointer:Option<usize>,
    rr_time:usize,
}

impl std::default::Default for Scheduler {
    fn default() -> Self {
        Scheduler { cycles_until_rr:SCHEDULE_THRESHOLD, rr_pointer:None, rr_time:RR_ROUNDS }
    }
}

impl SimtxScheduler for Scheduler {
    fn schedule(simulator:&mut Warp<Self>) -> Option<usize> {
        simulator.current_path =
        if simulator.paths.is_empty() { 
            simulator.current_path = None;
            simulator.scheduler.rr_pointer = None;
            simulator.scheduler.cycles_until_rr = SCHEDULE_THRESHOLD;
            None
        } else {

            //println!("SCHEDULING {:x?}", simulator.paths);
            // If it is RR time, start RR at path 0
            let next = if simulator.scheduler.cycles_until_rr == 0 {
                simulator.scheduler.cycles_until_rr = SCHEDULE_THRESHOLD;

                simulator.scheduler.rr_pointer = Some(0);
                simulator.scheduler.rr_time = RR_ROUNDS;

                //println!("START RR");
                Some(0)

            // If we are doing RR
            } else if let Some(ptr) = simulator.scheduler.rr_pointer {
                // Compute the next pointer (is the time-slice finished or not)
                let nptr = if simulator.scheduler.rr_time != 0 {
                    simulator.scheduler.rr_time -= 1;
                    ptr
                } else {
                    simulator.scheduler.rr_time = RR_ROUNDS;
                    ptr + 1
                };

                // Compute whether we finished RR or not
                let next = (nptr != simulator.paths.len()).then(|| nptr);

                //println!("CONTINUE RR {:?}", next);
                // Save and send the result
                simulator.scheduler.rr_pointer = next;
                next
            } else { None }; // If we are still doing MinPC (no RR triggered)

            // Send the RR-computed path id if any, or compute the MinPC either
            next.or_else(|| {
                simulator.scheduler.cycles_until_rr -= 1;

                //println!("FUCK THE SYSTEM");
                let mut copy : Vec<(usize, Path)>
                    = simulator.paths.iter().cloned().enumerate().collect();
                copy.sort_by_key(|(_,p)| p.fetch_pc);
                copy.first().map(|(i,_)| *i)
            })
        };
        simulator.current_path
    }
}
