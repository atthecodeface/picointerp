/*a Copyright

Licensed under the Apache License, Version 2.0 (the "License");
you may not use this file except in compliance with the License.
You may obtain a copy of the License at

  http://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software
distributed under the License is distributed on an "AS IS" BASIS,
WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
See the License for the specific language governing permissions and
limitations under the License.

@file    main.rs
@brief   Main executable for picointerpreter
 */

//a Imports
use std::fs::File;
extern crate clap;
use clap::{App, Arg};

//a Global constants for debug
// const DEBUG_MAIN      : bool = 1 == 0;

//a Main
//fp main
/// Run the application
fn main() {
    let matches = App::new("diagram")
        .about("SVG creator from a diagram descriptor")
        .author( "Gavin J Stark")
        .version( "0.1")
        .arg(Arg::with_name("output")
             .long("output")
             .help("Sets the output file to use")
             .required(false)
             .takes_value(true))
        .arg(Arg::with_name("debug")
             .short("d")
             .multiple(true))
        .arg(Arg::with_name("file")
             .help("Input files to read")
             .multiple(true))
        .get_matches();

}
