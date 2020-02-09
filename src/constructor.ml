(*
type 'a t =
  ('a, 'a, ('a, Name.t) Spine.t) Telescope.t
*)
type 'a arg_rec = ('a, 'a, ('a, Name.t) Spine.t) Telescope.t
type 'a arg     = 'a

type 'a t = (('a arg, 'a arg_rec) Sum.t, 'a, ('a, Name.t) Spine.t) Telescope.t
