//! Yes, I know that this is a silly example. However, it's necessary to meet
//! the requirements for the AP create task. It also demonstrates usage of the
//! crate quite well.

#![feature(allocator_api)]

use std::{
    alloc::Global,
    collections::{hash_map::Entry, HashMap},
    sync::Mutex,
};

use clap::Parser;
use linefeed::{Interface, ReadResult};
use vmem::{Arena, Error};

use crate::parsing::Command;

mod parsing;

fn main() -> anyhow::Result<()> {
    let interface = Interface::new("vmem-test")?;
    interface.set_prompt("[∴] ")?;

    let mut arenas: HashMap<String, Arena<'static, 'static, Global, Mutex<()>>> = HashMap::new();

    while let ReadResult::Input(command) = interface.read_line()? {
        match Command::try_parse_from(["[∴]"].into_iter().chain(command.split(' '))) {
            Ok(Command::Exit) => break,
            Ok(Command::Create { name, quantum }) => match arenas.entry(name.clone()) {
                Entry::Vacant(entry) => {
                    match Arena::<_, Mutex<()>>::create(name.leak(), quantum, None, Global) {
                        Ok(arena) => {
                            println!(
                                "Created arena {:?} with quantum {quantum:#x}",
                                arena.label()
                            );
                            entry.insert(arena);
                        }
                        Err(Error::InvalidQuantum) => {
                            println!("The quantum must be a power of two!");
                            continue;
                        }
                        _ => unreachable!(),
                    }
                }
                Entry::Occupied(_) => {
                    println!("There is already an arena named {name:?}");
                }
            },
            Ok(Command::AddSpan { arena, base, size }) => {
                match arenas.get(&arena) {
                    Some(arena) => match arena.add_span(base, size) {
                        Ok(_) => {
                            println!("Added span {base:#x}-{:#x}", base + size);
                        }
                        Err(Error::UnalignedSpan) => {
                            println!(
                                "The start and end of the span must be aligned to the quantum!"
                            );
                        }
                        Err(Error::WrappingSpan) => {
                            println!("That span would wrap around the address space!");
                        }
                        Err(Error::AllocZeroSize) => {
                            println!("The span must not have zero size!");
                        }
                        e => e?,
                    },
                    None => {
                        println!("There is no arena named {arena:?}");
                    }
                };
            }
            Ok(Command::Print { arena: None }) => {
                if !arenas.is_empty() {
                    println!();
                    for arena in arenas.values() {
                        println!("{:?}", arena);
                    }
                } else {
                    println!("There are no arenas to print!");
                }
            }
            Ok(Command::Print { arena: Some(arena) }) => {
                match arenas.get(&arena) {
                    Some(arena) => println!("\n{:?}", arena),
                    None => {
                        println!("There is no arena named {arena:?} :(");
                    }
                };
            }
            Ok(Command::Alloc {
                arena,
                policy,
                size,
                align,
                phase,
                nocross,
                min,
                max,
            }) => {
                match arenas.get(&arena) {
                    Some(arena) => {
                        let mut layout = match vmem::Layout::from_size_align(size, align) {
                            Some(layout) => layout,
                            None => {
                                println!("The size must be non-zero and the alignment must be a power of two!");
                                continue;
                            }
                        };
                        if let Some(phase) = phase {
                            layout = layout.with_phase(phase);
                        }
                        if let Some(nocross) = nocross {
                            layout = match layout.with_nocross(nocross) {
                                Some(layout) => layout,
                                None => {
                                    println!("The nocross must be a power of two greater than or equal to the size!");
                                    continue;
                                }
                            };
                        }
                        if let Some(min) = min {
                            layout = layout.with_min(min);
                        }
                        if let Some(max) = max {
                            layout = layout.with_max(max);
                        }
                        let ptr = arena.xalloc(layout, policy.into())?;
                        println!("Allocated {:#x} bytes at {:#x}", size, ptr);
                    }
                    None => {
                        println!("There is no arena named {arena:?} :(");
                    }
                };
            }
            Ok(Command::Free { arena, base }) => {
                match arenas.get(&arena) {
                    Some(arena) => match arena.free(base) {
                        Ok(_) => println!("Freed {:#x}", base),
                        Err(Error::NoSuchAllocation) => {
                            println!("There is no allocation at {:#x}", base)
                        }
                        _ => unreachable!(),
                    },
                    None => {
                        println!("There is no arena named {arena:?} :(");
                    }
                };
            }
            Ok(Command::Delete { arena: name }) => {
                match arenas.remove(&name) {
                    Some(_) => {
                        println!("Deleted arena {:?}!", name);
                    }
                    None => {
                        println!("There is no arena named {name:?} :(");
                    }
                };
            }
            Err(err) => {
                println!();
                err.print()?;
                println!();
                continue;
            }
        }
    }

    for (_, arena) in arenas {
        let label = arena.label();
        let _ =
            unsafe { String::from_raw_parts(label.as_ptr() as *mut _, label.len(), label.len()) };
    }

    Ok(())
}
