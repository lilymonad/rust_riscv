use machine::simtx::Warp;

mod loopaware;
pub use machine::simtx::scheduler::loopaware::Scheduler as LoopAwareScheduler;
mod timeshare;
pub use machine::simtx::scheduler::timeshare::Scheduler as TimeShareScheduler;
mod lexico;
pub use machine::simtx::scheduler::lexico::Scheduler as LexicoScheduler;

//mod proba;
//pub use proba::Scheduler as ProbaScheduler;

pub trait SimtxScheduler : Clone + Default {
    fn schedule(simulator:&mut Warp<Self>) -> Option<usize>;
}
