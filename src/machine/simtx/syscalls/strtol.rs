{
for i in self.warps[wid].alive_cores_ids() {
    let core = &mut self.warps[wid].cores[i];
    let mut str_addr = core.registers[10];
    let mut to_parse = String::new();
    let mut byte = mem.get_8(str_addr as usize);

    //println!("byte at 0x{:x}", str_addr);

    while byte != 0 {
        to_parse.push(byte as char);
        str_addr += 1;
        byte = mem.get_8(str_addr as usize);
    }

    //println!("strtol({})", to_parse);
    to_parse = to_parse.chars().filter(|x| x.is_numeric()).collect();
    let parsed = to_parse.parse()
        .expect(format!("couldnt parse {} to int", to_parse).as_str());
    //println!("strtol(\"{}\") = {}", to_parse, parsed);

    core.set_ri(10, parsed);
}
self.warps[wid].advance_pc(pathid, advance);
}
