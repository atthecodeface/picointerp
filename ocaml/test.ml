(** Copyright (C) 2018,  Gavin J Stark.  All rights reserved.
 *
 * Licensed under the Apache License, Version 2.0 (the "License");
 * you may not use this file except in compliance with the License.
 * You may obtain a copy of the License at
 *
 *   http://www.apache.org/licenses/LICENSE-2.0
 *
 * Unless required by applicable law or agreed to in writing, software
 * distributed under the License is distributed on an "AS IS" BASIS,
 * WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
 * See the License for the specific language governing permissions and
 * limitations under the License.
 *
 * @file   shm_ipc.ml
 * @brief  OCAML bindings for C stubs for SHM
 *
 *)


module Shm = struct
type t_point = {
  x:int;
  y:int;
}
let create x y : t_point = { x; y }
let midpoint p0 p1 = 
let x = (p0.x + p1.x) / 2 in
let y = (p0.y + p1.y) / 2 in
{ x; y}

end
