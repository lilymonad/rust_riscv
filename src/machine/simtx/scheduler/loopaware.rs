use machine::simtx::{Warp, scheduler::SimtxScheduler, implem::loops};
use std::{i32, collections::HashMap};

#[derive(Clone, Default)]
pub struct Scheduler {
}

impl SimtxScheduler for Scheduler {
    fn schedule(simulator:&mut Warp<Self>) -> Option<usize> {
        let mut grouped : HashMap<(i32, i32), Vec<(usize, i32)>> = HashMap::new();
        let mut copied : Vec<(usize, i32)> = simulator.paths.iter()
            .cloned()
            .map(|p| p.fetch_pc)
            .enumerate()
            .collect();

        // group paths by loop
        for (beg, end) in loops() {
            grouped.insert((*beg, *end), copied.drain_filter(|(_,x)| {
                *x >= *beg && *x <= *end
            }).collect());
        }

        // iterator over minimum of each groupe
        let grouped_mins = grouped
            .iter()
            .map(|((beg,end),vec)| {
                vec
                    .iter()
                    .min_by_key(|(pid1,pc1)| {
                        vec
                            .iter()
                            .filter(|(pid2,_)| pid2 != pid1)
                            .min_by_key(|(_,pc2)| (pc2 - pc1) % (end - beg))
                    })
                    .or(vec.first())
                    .unwrap()
            });

        // find min pc between single pc and "grouped min pc"
        let path = copied
            .iter()
            .chain(grouped_mins)
            //.map(|x| { println!("{:?}", x); x })
            .min_by_key(|(_,i)| i)
            .map(|(pid,x)| { /*println!("found : {:?}", (pid,x));*/ *pid });
        simulator.current_path = path;
        path
    }
}
