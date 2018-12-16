use std::io;

fn main() {
    let mut buf = String::new();
    io::stdin().read_line(&mut buf).ok();
    let prog = &buf;

    let mut data: [u8; 3000] = [0; 3000];

    let mut prog_ptr = 0;
    let mut data_ptr = 0;

    loop {
        match prog.chars().nth(prog_ptr) {
            None => break,
            Some(ch) => match ch {
                '>' => data_ptr += 1,
                '<' => data_ptr -= 1,
                '+' => data[data_ptr] += 1,
                '-' => data[data_ptr] -= 1,
                '.' => print!("{}", data[data_ptr] as char),
                ',' => print!("Not implemented"), // not implemented
                '[' => {
                    if data[data_ptr] == 0 {
                        let mut bracket_ctr = 0;
                        loop {
                            prog_ptr += 1;
                            let ch = prog.chars().nth(prog_ptr).unwrap();
                            if ch == '[' {
                                bracket_ctr += 1
                            } else if ch == ']' {
                                bracket_ctr -= 1
                            }
                            if bracket_ctr < 0 {
                                break
                            }
                        }
                    }
                },
                ']' => {
                    if data[data_ptr] == 0 {
                        let mut bracket_ctr = 0;
                        loop {
                            prog_ptr -= 1;
                            let ch = prog.chars().nth(prog_ptr).unwrap();
                            if ch == ']' {
                                bracket_ctr += 1
                            } else if ch == '[' {
                                bracket_ctr -= 1
                            }
                            if bracket_ctr < 0 {
                                break
                            }
                        }
                    }
                },
                 _ => (),
            }
        }
        prog_ptr += 1;
    }

}
