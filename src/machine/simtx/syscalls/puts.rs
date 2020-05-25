{
for i in self.warps[wid].alive_cores_ids() {
    let mut str_addr = self.warps[wid].cores[i].registers[10] as usize;
    let mut byte = mem.get_8(str_addr); let mut s = String::new();
    while byte != 0 {
        s.push(byte as char);
        str_addr += 1;
        byte = mem.get_8(str_addr);
    }
    println!("{}", s);
}
self.warps[wid].advance_pc(pathid, advance);
}
