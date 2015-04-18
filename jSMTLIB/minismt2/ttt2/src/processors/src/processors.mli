(* Copyright 2008 Martin Korp, Christian Sternagel, Harald Zankl
 * GNU Lesser General Public License
 *
 * This file is part of TTT2.
 * 
 * TTT2 is free software: you can redistribute it and/or modify it under
 * the terms of the GNU Lesser General Public License as published by the
 * Free Software Foundation, either version 3 of the License, or (at your
 * option) any later version.
 * 
 * TTT2 is distributed in the hope that it will be useful, but WITHOUT
 * ANY WARRANTY; without even the implied warranty of MERCHANTABILITY or
 * FITNESS FOR A PARTICULAR PURPOSE. See the GNU Lesser General Public
 * License for more details.
 * 
 * You should have received a copy of the GNU Lesser General Public
 * License along with TTT2. If not, see <http://www.gnu.org/licenses/>.
 *)

(** Processor Library
@author Martin Korp
@since  Fri Mar  6 14:29:43 CET 2009 *)

(** Provides various processors that can be used to prove termination of
TRSs automatically. In order to integrate new processors follow the
instruction in the file [processors.ml]. *)

(** {2 Module Rewriting} *)

(** Rewriting Functions
@author Martin Korp
@since  Mon Sep  1 12:22:31 CEST 2009 *)

(** Provides some basic functions that deal with the standard notions of
term rewriting. This module is an extension of the rewriting library.
I.e., it includes special labeling functions needed by the implemented
termination techniques. *)
module Rewritingx : sig
 module Function : Rewriting.FUNCTION
 module Variable : Rewriting.VARIABLE

 module Label : sig
  module F : Util.Index.ISOMORPHIC with
   type key = Function.t and type element = string
 
  module V : Util.Index.ISOMORPHIC with
   type key = Variable.t and type element = string

  type signature = F.t * V.t
  type t
  
  (** {3 Constructors and Destructors} *)

  val add_rlab : Function.t -> t -> t
  (** [add_rlab f l] adds [f] to the label [l] if [l] is a root label.
  @raise Failure "unknown label" if [l] is not a root label. *)
  val incr_curry : t -> t
  (** [incr_curry l] increments the value of [l] if [l] is a curry label.
  @raise Failure "unknown label" if [l] is not a curry label. *)
  val make_curry : int -> t
  (** [make_curry n] creates a curry label with value [n]. *)
  val make_dp : t
  (** [make_dp] creates a dp label. *)
  val make_height : int -> t
  (** [make_height n] creates a height label with value [n]. *)
  val make_rlab : Function.t list -> t
  (** [make_rlab fs] creates a root label with value [fs]. *)
  val make_slab : int -> t
  (** [make_slab n] creates a semantic label with value [n]. *)

  (** {3 Search Functions} *)

  val get_curry : t -> int
  (** [get_curry l] returns the value of [l] if [l] is a curry label.
  @raise Failure "unknown label" if [l] is not a curry label. *)
  val get_height : t -> int
  (** [get_height l] returns the value of [l] if [l] is a height label.
  @raise Failure "unknown label" if [l] is not a height label. *)
  val get_rlab : t -> Function.t list
  (** [get_rlab l] returns the value of [l] if [l] is a root label.
  @raise Failure "unknown label" if [l] is not a root label. *)
  val get_slab : t -> int
  (** [get_slab l] returns the value of [l] if [l] is a semantic label.
  @raise Failure "unknown label" if [l] is not a semantic label. *)

  (** {3 Properties} *)

  val is_curry : t -> bool
  (** [is_curry l] checks if [l] is a curry label. *)
  val is_dp : t -> bool
  (** [is_dp l] checks if [l] is a dp label. *)
  val is_height : t -> bool
  (** [is_height l] checks if [l] is a height label. *)
  val is_rlab : t -> bool
  (** [is_rlab l] checks if [l] is a root label. *)
  val is_slab : t -> bool
  (** [is_slab l] checks if [l] is a semantic label. *)

  (** {3 Miscellaneous} *)

  val copy : t -> t
  (** [copy l] returns a copy of [l]. *)
  val hash : t -> int
  (** [hash l] returns the hash value of [l]. *)

  (** {3 Compare Functions} *)

  val compare : t -> t -> int
  (** [compare l l'] compares the labels [l] and [l']. This function defines a
  total ordering on labels. *)
  val equal : t -> t -> bool
  (** [equal l l'] checks if [l] and [l'] are equal. This function is
  equivalent to [compare l l' = 0]. *)

  (** {3 Printers} *)

  val fprintf : Format.formatter -> t -> unit
  (** [fprintf fmt l] prints [l] using the OCaml module Format. *)
  val fprintfs : (Format.formatter -> Function.t -> signature -> signature)
   -> (Format.formatter -> Variable.t -> signature -> signature)
   -> Format.formatter -> t -> signature -> signature
  (** [fprintfs f g fmt l s] prints [l] using the [OCaml] module [Format].
  In difference to {!val: Processors.Rewritingx.Label.fprintf}, this function
  uses the information stored in the signature [s] to print function symbols
  and variables. *)
  val fprintfx : (Format.formatter -> Function.t -> signature -> signature)
   -> (Format.formatter -> Variable.t -> signature -> signature)
   -> Format.formatter -> t -> signature -> signature
  (** [fprintfx f g fmt l s] prints [l] in XML using the [OCaml] module
  [Format]. In difference to {!val: Processors.Rewritingx.Label.fprintf},
  this function uses the information stored in the signature [s] to print
  function symbols and variables. *)
  val to_string : t -> string
  (** [to_string l] returns a string that represents [l]. *)
 end

 module Signature : sig
  include Rewriting.STATEX with type label = Label.t

  (** {3 Constructors and Destructors} *)
  
  val add_rlab : Function.t -> Function.t -> t -> t
  (** [add_rlab f g s] updates the outermost root label of [g] by adding the
  function [f] to the top of the given list. Note that as a side effect the
  old signature changes all over. 
  @raise Not_found if [g] has no root label. *)
  val drop_curry : Function.t -> t -> Function.t
  (** [drop_curry f s] unlabels [f] if [f] admits a curry label.
  @raise Not_found otherwise. *)
  val drop_dp : Function.t -> t -> Function.t
  (** [drop_dp f s] unlabels [f] if [f] is a DP symbol.
  @raise Not_found otherwise. *)
  val drop_height : Function.t -> t -> Function.t
  (** [drop_height f s] unlabels [f] if [f] admits a height label.
  @raise Not_found otherwise. *)
  val drop_rlab : Function.t -> t -> Function.t
  (** [drop_rlab f s] unlabels [f] if [f] admits a root label.
  @raise Not_found otherwise. *)
  val drop_slab : Function.t -> t -> Function.t
  (** [drop_slab f s] unlabels [f] if [f] admits a semantic label.
  @raise Not_found otherwise. *)
  val incr_curry : Function.t -> t -> t
  (** [incr_curry f s] increments the outermost curry label of [f]. Note that
  as a side effect the old signature changes all over.
  @raise Not_found if [f] has no curry label. *)
  val modify_curry : Function.t -> int -> t -> t
  (** [modify_curry f n s] replaces the outermost curry label by a new curry
  label with value [n]. Note that as a side effect the old signature changes
  all over. 
  @raise Not_found if [f] has no curry label. *)
  val modify_height : Function.t -> int -> t -> t
  (** [modify_height f n s] replaces the outermost height label by a new height
  label with value [n]. Note that as a side effect the old signature changes
  all over. 
  @raise Not_found if [f] has no height label. *)
  val modify_rlab : Function.t -> Function.t list -> t -> t
  (** [modify_rlab f fs s] replaces the outermost root label by a new root
  label with value [fs]. Note that as a side effect the old signature changes
  all over. 
  @raise Not_found if [f] has no root label. *)
  val modify_slab : Function.t -> int -> t -> t
  (** [modify_slab f n s] replaces the outermost semantic label by a new
  semantic label with value [n]. Note that as a side effect the old signature
  changes all over. 
  @raise Not_found if [f] has no semantic label. *)
  val set_curry : ?arity:int -> Function.t -> int -> t -> Function.t * t
  (** [set_curry ~arity:a f n s] labels the function symbol [f] with the curry
  label [n]. Furthermore the arity of the labeled symbol is set to [a]. If
  [a] is not specified, the arity of the [f] is taken. Note that as a side
  effect the old signature changes all over. *)
  val set_dp : Function.t -> t -> Function.t * t
  (** [set_dp f s] labels the function symbol [f] as DP symbol. Note that as
  a side effect the old signature changes all over. *)
  val set_height : Function.t -> int -> t -> Function.t * t
  (** [set_height f n s] labels the function symbol [f] with height [n]. Note
  that as a side effect the old signature changes all over. *)
  val set_rlab : Function.t -> Function.t list -> t -> Function.t * t
  (** [set_rlab f fs s] labels the function symbol [f] with the root label
  [fs]. Note that as a side effect the old signature changes all over. *)
  val set_slab : Function.t -> int -> t -> Function.t * t
  (** [set_slab f n s] labels the function symbol [f] with the semantic label
  [n]. Note that as a side effect the old signature changes all over. *)
  
  (** {3 Search Functions} *)

  val get_curry : Function.t -> t -> int
  (** [get_curry f s] returns the value of the first curry label of [f].
  @raise Not_found if [f] does not admit a curry label. *)
  val get_height : Function.t -> t -> int
  (** [get_height f s] returns the value of the first height label of [f].
  @raise Not_found if [f] does not admit a height label. *)
  val get_rlab : Function.t -> t -> Function.t list
  (** [get_rlab f s] returns the value of the first root label of [f].
  @raise Not_found if [f] does not admit a root label. *)
  val get_slab : Function.t -> t -> int
  (** [get_slab f s] returns the value of the first semantic label of [f].
  @raise Not_found if [f] does not admit a semantic label. *)
  
  (** {3 Properties} *)

  val is_curry : Function.t -> t -> bool
  (** [is_curry f s] checks if [f] admits a curry label. *)
  val is_dp : Function.t -> t -> bool
  (** [is_dp f s] checks if [f] is a DP symbol. *)
  val is_height : Function.t -> t -> bool
  (** [is_height f s] checks if [f] admits a height label. *)
  val is_rlab : Function.t -> t -> bool
  (** [is_rlab f s] checks if [f] admits a root label. *)
  val is_slab : Function.t -> t -> bool
  (** [is_slab f s] checks if [f] admits a semantic label. *)

  (** {3 Printers} *)
 
  val fprintfx_fun : Format.formatter -> Function.t -> t -> t
  (** [fprintfx_fun fmt f s] prints [f] in XML using the [OCaml] module
  [Format]. This function uses the information stored in the signature
  [s] to print function symbols. If the name of a function symbol is not
  defined, a randomly generated name is printed. Note that as a side
  effect copies of [s] are changed too. Not tail-recursive. *)
  val fprintfx_var : Format.formatter -> Variable.t -> t -> t
  (** [fprintfx_var fmt x s] prints [x] in XML using the [OCaml] module
  [Format]. This function uses the information stored in the signature
  [s] to print variables. If the name of a variable is not defined, a
  randomly generated name is printed. Note that as a side effect copies
  of [s] are changed too. *)
  val to_stringx_fun : Function.t -> t -> string * t
  (** [to_stringx_fun f s] returns a formatted string that represents [f]
  in XML. This function uses the information stored in the signature [s] to
  print function symbols. If the name of a function symbol is not defined,
  a randomly generated name is printed. Note that as a side effect copies
  of [s] are changed too. Not tail-recursive. *)
  val to_stringx_var : Variable.t -> t -> string * t
  (** [to_stringx_var x s] returns a formatted string that represents [x]
  in XML. This function uses the information stored in the signature [s]
  to print variables. If the name of a variable is not defined, a randomly
  generated name is printed. Note that as a side effect copies of [s] are
  changed too. *)
 end

 module Monad : sig
  include Rewriting.MONADX with
   type label = Label.t and type state = Signature.t

  (** {3 Labeling Constructors and Destructors} *)
  
  (** {4 Generic Labelings } *)
  
  val add_int : ?arity:int -> Function.t -> int -> Function.t t
  (** [add_int ~arity:a i f] adds integer label [i] to [f] and sets
  its arity to [~arity]. Labels can be stacked. *)
  val drop_int : Function.t -> Function.t t
  (** [drop_int f] drops integer label of [f] from the top of the
  stack. Note that the arity of [f] is not changed by unlabeling.
  @raise No_int_label if [f] has no integer label *)
  val get_int : Function.t -> int t
  (** [get_int f] returns integer label of [f] on from the top of
  stack.
  @raise  No_int_label if [f] has no integer label. *)
  val is_int : Function.t -> bool t
  (** [is_int f] checks if [f] has an integer label*)

  (** {4 Specific Labelings } *)

  val add_rlab : Function.t -> Function.t -> unit t
  (** [add_rlab f g] is equivalent to
  {!val: Processors.Rewritingx.Signature.add_rlab} except that the signature is
  encapsulated in a monad. If [g] has no root label then the returned monad
  represents the error "not found". Note that as a side effect the underlying
  signature changes all over. *)
  val drop_curry : Function.t -> Function.t t
  (** [drop_curry f] is equivalent to
  {!val: Processors.Rewritingx.Signature.drop_curry} except that the result is
  encapsulated in a monad. If [f] is not labeled with a curry label, then the
  returned monad represents the error "not found". *)
  val drop_dp : Function.t -> Function.t t
  (** [drop_dp f] is equivalent to
  {!val: Processors.Rewritingx.Signature.drop_dp} except that the result is
  encapsulated in a monad. If [f] is not a DP symbol, then the returned monad
  represents the error "not found". *)
  val drop_height : Function.t -> Function.t t
  (** [drop_height f] is equivalent to
  {!val: Processors.Rewritingx.Signature.drop_height} except that the result
  is encapsulated in a monad. If [f] is not labeled with a height label, then
  the returned monad represents the error "not found". *)
  val drop_rlab : Function.t -> Function.t t
  (** [drop_rlab f] is equivalent to
  {!val: Processors.Rewritingx.Signature.drop_rlab} except that the result is
  encapsulated in a monad. If [f] is not labeled with a root label, then the
  returned monad represents the error "not found". *)
  val drop_slab : Function.t -> Function.t t
  (** [drop_slab f] is equivalent to
  {!val: Processors.Rewritingx.Signature.drop_slab} except that the result is
  encapsulated in a monad. If [f] is not labeled with a semantic label, then
  the returned monad represents the error "not found". *)
  val incr_curry : Function.t -> unit t
  (** [incr_curry f] is equivalent to
  {!val: Processors.Rewritingx.Signature.incr_curry} except that the signature
  is encapsulated in a monad. If [f] has no curry label then the returned monad
  represents the error "not found". Note that as a side effect the underlying
  signature changes all over. *)
  val modify_curry : Function.t -> int -> unit t
  (** [modify_curry f n] is equivalent to
  {!val: Processors.Rewritingx.Signature.modify_curry} except that the signature
  is encapsulated in a monad. If [f] has no curry label then the returned monad
  represents the error "not found". Note that as a side effect the underlying
  signature changes all over. *)
  val modify_height : Function.t -> int -> unit t
  (** [modify_height f n] is equivalent to
  {!val: Processors.Rewritingx.Signature.modify_height} except that the
  signature is encapsulated in a monad. If [f] has no height label then the
  returned monad represents the error "not found". Note that as a side effect
  the underlying signature changes all over. *)
  val modify_rlab : Function.t -> Function.t list -> unit t
  (** [modify_rlab f fs] is equivalent to
  {!val: Processors.Rewritingx.Signature.modify_rlab} except that the signature
  is encapsulated in a monad. If [f] has no root label then the returned monad
  represents the error "not found". Note that as a side effect the underlying
  signature changes all over. *)
  val modify_slab : Function.t -> int -> unit t
  (** [modify_slab f n] is equivalent to
  {!val: Processors.Rewritingx.Signature.modify_slab} except that the
  signature is encapsulated in a monad. If [f] has no semantic label then
  the returned monad represents the error "not found". Note that as a side
  effect the underlying signature changes all over. *)
  val set_curry : ?arity:int -> Function.t -> int -> Function.t t
  (** [set_curry ~arity:a f n] is equivalent to
  {!val: Processors.Rewritingx.Signature.set_curry} except that the result is
  encapsulated in a monad. Note that as a side effect the underlying signature
  changes all over. *)
  val set_dp : Function.t -> Function.t t
  (** [set_dp f] is equivalent to
  {!val: Processors.Rewritingx.Signature.set_dp} except that the result is
  encapsulated in a monad. Note that as a side effect the underlying signature
  changes all over. *)
  val set_height : Function.t -> int -> Function.t t
  (** [set_height f n] is equivalent to
  {!val: Processors.Rewritingx.Signature.set_height} except that the result is
  encapsulated in a monad. Note that as a side effect the underlying signature
  changes all over. *)
  val set_rlab : Function.t -> Function.t list -> Function.t t
  (** [set_rlab f fs] is equivalent to
  {!val: Processors.Rewritingx.Signature.set_rlab} except that the result is
  encapsulated in a monad. Note that as a side effect the underlying signature
  changes all over. *)
  val set_slab : Function.t -> int -> Function.t t
  (** [set_slab f n] is equivalent to
  {!val: Processors.Rewritingx.Signature.set_slab} except that the result is
  encapsulated in a monad. Note that as a side effect the underlying signature
  changes all over. *)

  (** {3 Labeling Search Functions} *)

  val get_curry : Function.t -> int t
  (** [get_curry f] is equivalent to
  {!val: Processors.Rewritingx.Signature.get_curry} except that the result is
  encapsulated in a monad. If [f] is not labeled with a curry label, then the
  returned monad represents the error "not found". *)
  val get_height : Function.t -> int t
  (** [get_height f] is equivalent to
  {!val: Processors.Rewritingx.Signature.get_height} except that the result is
  encapsulated in a monad. If [f] is not labeled with a height label, then the
  returned monad represents the error "not found". *)
  val get_rlab : Function.t -> Function.t list t
  (** [get_rlab f] is equivalent to
  {!val: Processors.Rewritingx.Signature.get_rlab} except that the result is
  encapsulated in a monad. If [f] is not labeled with a root label, then the
  returned monad represents the error "not found". *)
  val get_slab : Function.t -> int t
  (** [get_slab f] is equivalent to
  {!val: Processors.Rewritingx.Signature.get_slab} except that the result is
  encapsulated in a monad. If [f] is not labeled with a semantic label, then
  the returned monad represents the error "not found". *)

  (** {3 Labeling Properties} *)

  val is_curry : Function.t -> bool t
  (** [is_curry f] is equivalent to
  {!val: Processors.Rewritingx.Signature.is_curry} except that the result is
  encapsulated in a monad. *)
  val is_dp : Function.t -> bool t
  (** [is_curry f] is equivalent to
  {!val: Processors.Rewritingx.Signature.is_dp} except that the result is
  encapsulated in a monad. *)
  val is_height : Function.t -> bool t
  (** [is_curry f] is equivalent to
  {!val: Processors.Rewritingx.Signature.is_height} except that the result is
  encapsulated in a monad. *)
  val is_rlab : Function.t -> bool t
  (** [is_curry f] is equivalent to
  {!val: Processors.Rewritingx.Signature.is_rlab} except that the result is
  encapsulated in a monad. *)
  val is_slab : Function.t -> bool t
  (** [is_curry f] is equivalent to
  {!val: Processors.Rewritingx.Signature.is_slab} except that the result is
  encapsulated in a monad. *)

  (** {3 Printers} *)

  val fprintfx_fun : Function.t -> Format.formatter -> unit t
  (** [fprintfx_fun f fmt] is equivalent to
  {!val: Processors.Rewritingx.Signature.fprintfx_fun} except that the
  signature is encapsulated in a monad. Note that as a side effect the
  old signature is changed too. Not tail-recursive. *)
  val fprintfx_var : Variable.t -> Format.formatter -> unit t
  (** [fprintfx_var x fmt] is equivalent to
  {!val: Processors.Rewritingx.Signature.fprintfx_var} except that the
  signature is encapsulated in a monad. Note that as a side effect the
  old signature is changed too. *)
  val to_stringx_fun : Function.t -> string t
  (** [to_stringx_fun f] is equivalent to
  {!val: Processors.Rewritingx.Signature.to_stringx_fun} except that the
  signature is encapsulated in a monad. Note that as a side effect the
  old signature is changed too. Not tail-recursive. *)
  val to_stringx_var : Variable.t -> string t
  (** [to_stringx_var x] is equivalent to
  {!val: Processors.Rewritingx.Signature.to_stringx_var} except that the
  signature is encapsulated in a monad. Note that as a side effect the
  old signature is changed too. *)
 end

 module Position : sig
  include Rewriting.POSITION

  (** {3 Printers} *)

  val fprintfx : t -> Format.formatter -> unit Monad.t
  (** [fprintfx p fmt] prints [p] in XML using the [OCaml] module [Format]. *)
  val to_stringx : t -> string Monad.t
  (** [to_stringx p] returns a formatted string that represents [p] in XML. *)
 end

 module Parser : Rewriting.PARSER
  with type state = Signature.t and type input = Parsec.StringInput.t

 module Term : sig
  include Rewriting.TERM with type 'a m = 'a Monad.t and type 'a p = 'a Parser.t
    and type 'a x = 'a Parser.Xml.t

  (** {3 Labeling and Unlabeling Functions} *)

  val label_dp : t -> t m
  (** [label_dp t] labels the root symbol of [t] as dependency pair symbol. *)
  val label_height : int -> t -> t m
  (** [label_height h t] labels all function symbols of [t] with height [h]. *)
  val unlabel_dp : t -> t m
  (** [unlabel_dp t] checks if the root symbol of [t] is a dependency pair
  symbol. If that is the case, the original symbol is restored. Otherwise
  [t] is returned. *)
  val unlabel_height : t -> t m
  (** [unlabel_height t] unlabels all function symbol that have been labeled
  with a height label. Note that if [t] does not contains a function symbol
  with height label then [t] is returned. *)
  val spine : t -> Position.t -> t m
  (* [spine t p] returns a string consisting of the symbols to position [p]. *)

  (** {3 Printers} *)

  val fprintfx : t -> Format.formatter -> unit m
  (** [fprintfx t fmt] prints [t] in XML using the [OCaml] module [Format].
  This function uses the information stored in the underlying signature to
  print function symbols and variables. If the name of a function symbol or
  variable is not defined, a randomly generated name is printed. Note that
  as a side effect copies of the underlying signature are changed too. This
  function is not tail-recursive. *)
  val to_stringx : t -> string m
  (** [to_stringx t] returns a formatted string that represents [t] in XML.
  This function uses the information stored in the underlying signature to
  print function symbols and variables. If the name of a function symbol or
  variable is not defined, a randomly generated name is printed. Note that
  as a side effect copies of the underlying signature are changed too. This
  function is not tail-recursive. *)
 end

 module Context : sig
  include Rewriting.CONTEXT with type term = Term.t

  (** {3 Printers} *)

  val fprintfx : t -> Format.formatter -> unit m
  (** [fprintfx c fmt] prints [c] in XML using the [OCaml] module [Format].
  This function uses the information stored in the underlying signature to
  print function symbols and variables. If the name of a function symbol or
  variable is not defined, a randomly generated name is printed. Note that
  as a side effect copies of the underlying signature are changed too. This
  function is not tail-recursive. *)
  val to_stringx : t -> string m
  (** [to_stringx c] returns a formatted string that represents [c] in XML.
  This function uses the information stored in the underlying signature to
  print function symbols and variables. If the name of a function symbol or
  variable is not defined, a randomly generated name is printed. Note that
  as a side effect copies of the underlying signature are changed too. This
  function is not tail-recursive. *)
 end
 
 module Substitution : sig
  include Rewriting.SUBSTITUTION with
   type term = Term.t and type context = Context.t

  (** {3 Printers} *)

  val fprintfx : t -> Format.formatter -> unit m
  (** [fprintfx s fmt] prints [s] in XML using the [OCaml] module [Format].
  This function uses the information stored in the underlying signature to
  print function symbols and variables. If the name of a function symbol or
  variable is not defined, a randomly generated name is printed. Note that
  as a side effect copies of the underlying signature are changed too. This
  function is not tail-recursive. *)
  val to_stringx : t -> string m
  (** [to_stringx s] returns a formatted string that represents [s] in XML.
  This function uses the information stored in the underlying signature to
  print function symbols and variables. If the name of a function symbol or
  variable is not defined, a randomly generated name is printed. Note that
  as a side effect copies of the underlying signature are changed too. This
  function is not tail-recursive. *)
 end
 
 module Elogic : Rewriting.ELOGIC with
  type 'a m = 'a Monad.t and type substitution = Substitution.t and
  type term = Term.t
 
 module Rule : sig
  include Rewriting.RULE with
   type 'a m = 'a Monad.t and type 'a p = 'a Parser.t
    and type substitution = Substitution.t and type term = Term.t
    and type 'a x = 'a Parser.Xml.t

  (** {3 Printers} *)

  val fprintfx : t -> Format.formatter -> unit m
  (** [fprintfx r fmt] prints [r] in XML using the [OCaml] module [Format].
  This function uses the information stored in the underlying signature to
  print function symbols and variables. If the name of a function symbol or
  variable is not defined, a randomly generated name is printed. Note that
  as a side effect copies of the underlying signature are changed too. This
  function is not tail-recursive. *)
  val to_stringx : t -> string m
  (** [to_stringx r] returns a formatted string that represents [r] in XML.
  This function uses the information stored in the underlying signature to
  print function symbols and variables. If the name of a function symbol or
  variable is not defined, a randomly generated name is printed. Note that
  as a side effect copies of the underlying signature are changed too. This
  function is not tail-recursive. *)
 end
 
 module Trs : sig
  include Rewriting.TRS with
   type 'a m = 'a Monad.t and type 'a p = 'a Parser.t
    and type rule = Rule.t and type term = Term.t
    and type 'a x = 'a Parser.Xml.t

  (** {3 Miscellaneous} *)

  val etcap : term -> t -> term m
  (** [etcap t r] modifies the term [t] such that it can be checked whether
  an instance of [t] rewrites to some term [u] with respect to the TRS [r],
  by using ground matching. *)
  val icap : term -> t -> term m
  (** [icap t r] modifies the term [t] such that it can be checked whether
  an instance of [t] rewrites to some term [u] with respect to the innermost
  rewrite relation induced by the TRS [r], by using unification. *)
  val is_strongly_nonoverlapping : t -> bool m
  (** [is_strongly_nonoverlapping r], checks if there are no overlaps after
  linearizing [r]. *)
  val linear : t -> t m
  (** [linear r] returns a complete linearization of [r]. I.e., all possible
  linearizations of left-hand sides are taken into consideration. *)
  val linearize : t -> t m
  (** [linearize r] linearizes [r]. In difference to
  {!val: Processors.Rewritingx.Trs.linear} only one linearization is
  computed. *)
  val recursors : t -> rule list
  (** [recursors r] returns all rewrite rules of [r] whose right-hand side
  contains a defined symbol. *)
  val sharp : t -> (Function.t * t) m
  (** [sharp r] transforms [r] into a rewrite system which can be used to
  compute the set of right-hand sides of forward closures via tree automata
  completion. *)
  val tcap : term -> t -> term m
  (** [tcap t r] modifies the term [t] such that it can be checked whether
  an instance of [t] rewrites to some term [u] with respect to the the TRS
  [r], by using unification. *)

  (** {3 Printers} *)

  val fprintfx : t -> Format.formatter -> unit m
  (** [fprintfx r fmt] prints [r] in XML using the [OCaml] module [Format].
  This function uses the information stored in the underlying signature to
  print function symbols and variables. If the name of a function symbol or
  variable is not defined, a randomly generated name is printed. Note that
  as a side effect copies of the underlying signature are changed too. This
  function is not tail-recursive. *)
  val to_stringx : t -> string m
  (** [to_stringx r] returns a formatted string that represents [r] in XML.
  This function uses the information stored in the underlying signature to
  print function symbols and variables. If the name of a function symbol or
  variable is not defined, a randomly generated name is printed. Note that
  as a side effect copies of the underlying signature are changed too. This
  function is not tail-recursive. *)
 end
 
 module Diagram: sig
  include Rewriting.DIAGRAM with
   type 'a m = 'a Monad.t and type term = Term.t

  (** {3 Miscellaneous} *)
  (** {3 Printers} *)
 end

 module Rewrite : Rewriting.REWRITE with
  type term = Term.t and type trs = Trs.t

 module Filtering : sig
  type filter = Collapsing of int | List of int list;;
  type t

  (** Constructors and Destructors *)

  val add : Function.t -> filter -> t -> t
  (** [add f filter af] adds a binding from [f] to [filter] to the argument
  filtering [af]. If [af] consists already a binding for [f], [af] remains
  unchanged. *)
  val empty : t
  (** [empty] returns and empty argument filtering. *)
  val of_list : (Function.t * filter) list -> t
  (** [of_list xs] computes an argument filtering containing all bindings of
  [xs]. Note that multiples of one and the same binding are added only once. *)
  val to_list : t -> (Function.t * filter) list
  (** [to_list af] returns [af] as a list.  *)

  (** Search Functions *)

  val find : Function.t -> t -> filter
  (** [find f af] returns the arguments to which the function symbol [f] is
  mapped with respect to the argument filtering [af].
  @raise Not_found if [af] does not contain a binding for [f]. *)

  (** Apply Functions *)

  val apply_rule : t -> Rule.t -> Rule.t
  (** [apply_rule af r] applies the argument filtering [af] to the left- and
  right-hand sides of rule [r].
  @raise Failure "incomplete filtering" if [af] does not contain a binding
  for all function symbols occurring in [r]. *)
  val apply_term : t -> Term.t -> Term.t
  (** [apply_term af t] applies the argument filtering [af] to the term [t].
  @raise Failure "incomplete filtering" if [af] does not contain a binding
  for all function symbols occurring in [t]. *)
  val apply_trs : t -> Trs.t -> Trs.t
  (** [apply_trs af r] applies the argument filtering [af] to the TRS [r].
  @raise Failure "incomplete filtering" if [af] does not contain a binding
  for all function symbols occurring in [r]. *)

  (** {3 Printers} *)

  val fprintf : Format.formatter -> t -> unit
  (** [fprintf fmt af] prints [af] using the [OCaml] module [Format]. *)
  val fprintfm : Format.formatter -> t -> unit Monad.t
  (** [fprintfm fmt af] prints [af] using the [OCaml] module [Format].
  Function symbols are represented by their names registered in the
  underlying signature. If the name of a function symbol is not defined,
  a randomly generated name is printed. Note that as a side effect copies
  of the underlying signature are changed too. *)
  val fprintfx : t -> Format.formatter -> unit Monad.t
  (** [fprintfx af fmt] prints [af] in XML using the [OCaml] module [Format].
  Function symbols are represented by their names registered in the
  underlying signature. If the name of a function symbol is not defined,
  a randomly generated name is printed. Note that as a side effect copies
  of the underlying signature are changed too. This function is not
  tail-recursive. *)
  val to_string : t -> string
  (** [to_string af] returns a formatted string that represents [af]. *)
  val to_stringm : t -> string Monad.t
  (** [to_stringm af] returns a formatted string that represents [af].
  Function symbols are represented by their names registered in the
  underlying signature. If the name of a function symbol is not defined,
  a randomly generated name is used. Note that as a side effect copies
  of the underlying signature are changed too. *)
  val to_stringx : t -> string Monad.t
  (** [to_stringx af] returns a formatted string that represents [af] in
  XML. Function symbols are represented by their names registered in the
  underlying signature. If the name of a function symbol is not defined,
  a randomly generated name is printed. Note that as a side effect copies
  of the underlying signature are changed too. This function is not
  tail-recursive. *)
 end
 
 module Graph : sig
  include Util.Graph.SIGNATURE with
   type node = Rule.t and type edge = Rule.t * Rule.t

  (** {3 Printers} *)

  val fprintfm : Format.formatter -> t -> unit Monad.t
  (** [fprintfm fmt g] prints [g] using the [OCaml] module [Format].
  Function symbols and variables are represented by their names registered
  in the underlying signature. If the name of a function symbol or variable
  is not defined, a randomly generated name is printed. Note that as a side
  effect copies of the underlying signature are changed too. This function
  is not tail-recursive. *)
  val fprintfx : t -> Format.formatter -> unit Monad.t
  (** [fprintfx g fmt] prints [g] in XML using the [OCaml] module [Format].
  This function uses the information stored in the underlying signature to
  print function symbols and variables. If the name of a function symbol or
  variable is not defined, a randomly generated name is printed. Note that
  as a side effect copies of the underlying signature are changed too. This
  function is not tail-recursive. *)
  val to_stringm : t -> string Monad.t
  (** [to_stringm g] returns a formatted string that represents [g].
  Function symbols and variables are represented by their names registered
  in the underlying signature. If the name of a function symbol or variable
  is not defined, a randomly generated name is used. Note that as a side
  effect copies of the underlying signature are changed too. This function
  is not tail-recursive. *)
  val to_stringx : t -> string Monad.t
  (** [to_stringx g] returns a formatted string that represents [g] in XML.
  This function uses the information stored in the underlying signature to
  print function symbols and variables. If the name of a function symbol or
  variable is not defined, a randomly generated name is printed. Note that
  as a side effect copies of the underlying signature are changed too. This
  function is not tail-recursive. *)
 end

 module Projection : sig
  type t

  (** Constructors and Destructors *)

  val add : Function.t -> int -> t -> t
  (** [add f ps sp] adds a binding from [f] to [ps] to the simple projection
  [sp]. If [sp] consists already a binding for [f], [sp] remains unchanged. *)
  val empty : t
  (** [empty] returns and empty simple projection. *)
  val of_list : (Function.t * int) list -> t
  (** [of_list xs] computes a simple projection containing all bindings of
  [xs]. Note that multiples of one and the same binding are added only once. *)
  val to_list : t -> (Function.t * int) list
  (** [to_list sp] returns [sp] as a list. *)

  (** Search Functions *)

  val find : Function.t -> t -> int
  (** [find f sp] returns the argument to which the function symbol [f] is
  mapped with respect to the simple projection [sp].
  @raise Not_found if [sp] does not contain a binding for [f]. *)

  (** Apply Functions *)

  val apply_rule : t -> Rule.t -> Rule.t
  (** [apply_rule sp r] applies the simple projection [sp] to the left- and
  right-hand sides of rule [r].
  @raise Failure "incomplete filtering" if [sp] does not contain a binding
  for all function symbols occurring in [r]. *)
  val apply_term : t -> Term.t -> Term.t
  (** [apply_term sp t] applies the simple projection [sp] to the term [t].
  @raise Failure "incomplete filtering" if [sp] does not contain a binding
  for all function symbols occurring in [t]. *)
  val apply_trs : t -> Trs.t -> Trs.t
  (** [apply_trs sp r] applies the simple projection [sp] to the TRS [r].
  @raise Failure "incomplete filtering" if [sp] does not contain a binding
  for all function symbols occurring in [r]. *)

  (** {3 Printers} *)

  val fprintf : Format.formatter -> t -> unit
  (** [fprintf fmt sp] prints [sp] using the [OCaml] module [Format]. *)
  val fprintfm : Format.formatter -> t -> unit Monad.t
  (** [fprintfm fmt sp] prints [sp] using the [OCaml] module [Format].
  Function symbols are represented by their names registered in the
  underlying signature. If the name of a function symbol is not defined,
  a randomly generated name is printed. Note that as a side effect copies
  of the underlying signature are changed too. This function is not
  tail-recursive. *)
  val fprintfx : t -> Format.formatter -> unit Monad.t
  (** [fprintfx sp fmt] prints [sp] in XML using the [OCaml] module [Format].
  Function symbols are represented by their names registered in the
  underlying signature. If the name of a function symbol is not defined,
  a randomly generated name is printed. Note that as a side effect copies
  of the underlying signature are changed too. This function is not
  tail-recursive. *)
  val to_string : t -> string
  (** [to_string sp] returns a formatted string that represents [sp]. *)
  val to_stringm : t -> string Monad.t
  (** [to_stringm sp] returns a formatted string that represents [sp].
  Function symbols are represented by their names registered in the
  underlying signature. If the name of a function symbol is not defined,
  a randomly generated name is used. Note that as a side effect copies
  of the underlying signature are changed too. This function is not
  tail-recursive. *)
  val to_stringx : t -> string Monad.t
  (** [to_stringx sp] returns a formatted string that represents [sp] in
  XML. Function symbols are represented by their names registered in the
  underlying signature. If the name of a function symbol is not defined,
  a randomly generated name is printed. Note that as a side effect copies
  of the underlying signature are changed too. This function is not
  tail-recursive. *)
 end
end

(** {2 Module Problem} *)

(** Problem
@author Martin Korp
@since  Mon Sep  1 12:22:31 CEST 2009 *)

(** Defines the different termination problems that are supported by TTT2. *)
module Problem : sig
 type graph = Complete | Partial of Rewritingx.Graph.t
 type language = All | Constructor;;
 type strategy = Full | Innermost | Outermost
 type problem
 type t

 (** {3 Constructors} *)

 val adapt : problem -> t -> t
 (** [adapt p' p] replaces the internal problem of [p] by [p']. *)
 val create_cp : Rewritingx.Trs.t -> Rewritingx.Trs.t -> problem
 (** [create_cp s w] returns the CP problem consisting of the strict TRS [s]
 and the weak TRS [w]. *)
 val create_dp : Rewritingx.Trs.t -> Rewritingx.Trs.t -> graph -> problem
 (** [create_dp dp trs dg] returns the DP problem consisting of the dependency
 pairs [dp], the TRS [trs], and the dependency graph [dg]. *)
 val create_rp : Rewritingx.Trs.t -> Rewritingx.Trs.t -> problem
 (** [create_rp s w] returns the relative termination problem consisting of
 the strict TRS [s] and the weak TRS [w]. *)
 val create_sp : Rewritingx.Trs.t -> problem
 (** [create_sp trs] returns the standard termination problem consisting of
 the TRS [trs]. *)
 val make_cp : language -> strategy -> Rewritingx.Trs.t -> Rewritingx.Trs.t -> t
 (** [make_cp l strategy s w] returns the [strategy]-CP problem consisting of
 the strict TRS [s] and the weak TRS [w]. The argument [l] specifies the set
 of terms of which termination should be proved. *)
 val make_dp : language -> strategy -> Rewritingx.Trs.t -> Rewritingx.Trs.t
  -> graph -> t
 (** [make_dp l strategy dp trs dg] returns the [strategy]-DP problem
 consisting of the dependency pairs [dp], the TRS [trs], and the dependency
 graph [dg]. The argument [l] specifies the set of terms of which termination
 should be proved. *)
 val make_rp : language -> strategy -> Rewritingx.Trs.t -> Rewritingx.Trs.t -> t
 (** [make_rp l strategy s w] returns the [strategy]-relative termination
 problem consisting of the strict TRS [s] and the weak TRS [w]. The argument
 [l] specifies the set of terms of which termination should be proved. *)
 val make_sp : language -> strategy -> Rewritingx.Trs.t -> t
 (** [make_sp l strategy trs] returns the [strategy]-termination problem
 consisting of the TRS [trs]. The argument [l] specifies the set of terms
 of which termination should be proved. *)
 val make_crp : language -> strategy -> Rewritingx.Trs.t -> t
 (** [make_crp l strategy trs] returns the confluence problem  consisting
 of the TRS [trs]. Only [l = All] and [strategy = Full] are currently
 supported. *)
 val sp_to_crp : t -> t
 (** [sp_to_crp p] turns standard termination problem into a confluence
 problem using the same TRS. Fails if [get_language p != All] or
 [get_strategy p != Full] *)
 val minimize : t -> t
 (** [minimize p] in case that [p] is a DP problem, the dependency graph of
 [p] is restricted to the current set of dependency pairs. Otherwise the
 problem remains unchanged. *)
 val set_dg : graph -> Rewritingx.Trs.t -> Rewritingx.Trs.t -> t -> t
 (** [set_dg dg dps trs p] replaces the dependency graph of the DP problem
 [p] by [dg]. Here [dg] is computed by [dps] and [trs]. Note that [None]
 represents the fully connected graph which has the
 dependency pairs of [p] as nodes.
 @raise Failure "not a DP problem" if [p] is not a DP problem. *)
 val set_dps : Rewritingx.Trs.t -> t -> t
 (** [set_dps dp p] replaces the dependency pairs of the DP problem [p] by [dp].
 @raise Failure "not a DP problem" if [p] is not a DP problem. *)
 val set_language : language -> t -> t
 (** [set_language l p] replaces the language of the problem [p] by [l]. *)
 val set_strategy : strategy -> t -> t
 (** [set_strategy s p] replaces the strategy of the problem [p] by [s]. *)
 val set_strict : Rewritingx.Trs.t -> t -> t
 (** [set_strict s p] replaces the strict TRS of the relative termination
 or CP problem [p] by [s].
 @raise Failure "not a relative termination or CP problem" if [p] is neither
 a relative termination problem nor a CP problem. *)
 val set_sw : Rewritingx.Trs.t -> Rewritingx.Trs.t -> t -> t
 (** [set_sw s w p] replaces the dependency pairs (TRS, strict TRS) of the
 dependency pair problem (standard termination problem, relative termination
 or CP problem) [p] by [s] and the TRS (weak TRS) of the dependency pair
 problem (relative termination or CP problem) by [w].
 @raise Failure "not a standard problem" if [p] is a standard termination
 problem and [w] is not the empty TRS. *)
 val set_trs : Rewritingx.Trs.t -> t -> t
 (** [set_trs trs p] replaces the TRS of [p] by [s] if [p] is a standard
 termination or DP problem.
 @raise Failure "not a standard termination or DP problem" if [p] is not
 a standard termination or DP problem. *)
 val set_weak : Rewritingx.Trs.t -> t -> t
 (** [set_weak w p] replaces the weak TRS of the relative termination or CP
 problem [p] by [s].
 @raise Failure "not a relative termination or CP problem" if [p] is neither
 a relative termination problem nor a CP problem. *)

 (** {3 Access Functions} *)

 val get_dg : t -> graph
 (** [get_dg p] returns the dependency graph of the DP problem [p]. Note
 that [None] represents the fully connected graph which has the dependency
 pairs of [p] as nodes.
 @raise Failure "not a DP problem" if [p] is not a DP problem. *)
 val get_cds : t -> Rewritingx.Diagram.t list
 (** [get_cds p] returns the critical diagrams of [p].
 @raise Failure "not a diagram problem" if [p] is not a diagram problem. *)
 val get_dps : t -> Rewritingx.Trs.t
 (** [get_dps p] returns the dependency pairs of the DP problem [p].
 @raise Failure "not a DP problem" if [p] is not a DP problem. *)
 val get_language : t -> language
 (** [get_language p] returns the language of the termination problem [p]. *)
 val get_strategy : t -> strategy
 (** [get_strategy p] returns the strategy of the termination problem [p]. *)
 val get_strict : t -> Rewritingx.Trs.t
 (** [get_strict p] returns the strict TRS of the relative termination or CP
 problem [p].
 @raise Failure "not a relative termination or CP problem" if [p] is neither
 a relative termination problem nor a CP problem. *)
 val get_trs : t -> Rewritingx.Trs.t
 (** [get_trs p] returns the TRS of [p] if [p] is a standard termination or
 DP problem.
 @raise Failure "not a standard termination or DP problem" if [p] is not a
 standard termination problem. *)
 val get_weak : t -> Rewritingx.Trs.t
 (** [get_weak p] returns the weak TRS of the relative termination or CP
 problem [p].
 @raise Failure "not a relative termination or CP problem" if [p] is neither
 a relative termination problem nor a CP problem. *)
 val get_sw : t -> Rewritingx.Trs.t * Rewritingx.Trs.t
 (** [get_sw p] returns the dependency pairs (TRS, strict TRS) as well as
 the TRS (weak TRS) of the dependency pair problem (standard termination
 problem, relative termination or CP problem) [p]. *)

 (** {3 Properties} *)

 val exists : (Rewritingx.Trs.t -> bool) -> t -> bool
 (** [exists f p] checks if at least one of the TRSs of [p] satisfy the
 predicate [f]. *)
 val existsm : (Rewritingx.Trs.t -> bool Rewritingx.Monad.t) -> t
  -> bool Rewritingx.Monad.t
 (** [existsm f p] is equivalent to {!val: Processors.Problem.exists}
 except that the result is encapsulated in a monad. *)
 val for_all : (Rewritingx.Trs.t -> bool) -> t -> bool
 (** [for_all f p] checks if the TRSs of [p] satisfy the predicate [f]. *)
 val for_allm : (Rewritingx.Trs.t -> bool Rewritingx.Monad.t) -> t
  -> bool Rewritingx.Monad.t
 (** [for_allm f p] is equivalent to {!val: Processors.Problem.for_all}
 except that the result is encapsulated in a monad. *)
 val is_al : t -> bool
 (** [is_al p] checks if termination of [p] should be proved for all terms. *)
 val is_cl : t -> bool
 (** [is_cl p] checks if termination of [p] should be proved just for
 constructor terms. *)
 val is_cp : t -> bool
 (** [is_cp p] checks if [p] is a CP problem. *)
 val is_crp : t -> bool
 (** [is_crp p] checks if [p] is a Church Rosser problem. *)
 val is_ddp : t -> bool
 (** [is_ddp p] checks if [p] is a Diagram problem. *)
 val is_auxp : t -> bool
 (** [is_auxp] checks if [p] is a AuxRT problem. *)
 val is_dp : t -> bool
 (** [is_dp p] checks if [p] is a DP problem. *)
 val is_empty : t -> bool
 (** [is_empty p] checks if the problem [p] is empty, i.e., trivially
 terminating. *)
 val is_ft : t -> bool
 (** [is_ft p] checks if [p] uses the full rewriting strategy. *)
 val is_it : t -> bool
 (** [is_it p] checks if [p] uses the innermost strategy. *)
 val is_ot : t -> bool
 (** [is_ot p] checks if [p] uses the outermost strategy. *)
 val is_rp : t -> bool
 (** [is_rp p] checks if [p] is a relative termination problem. *)
 val is_sp : t -> bool
 (** [is_sp p] checks if [p] is a standard termination problem. *)

 (** {3 Compare Functions} *)

 val equal : t -> t -> bool
 (** [equal p p'] checks if [p] and [p'] are equal. *)

 (** {3 Printers} *)

 val fprintf : ?g:bool -> Format.formatter -> t -> unit
 (** [fprintf ~g:g fmt p] prints [p] using the [OCaml] module [Format]. If
 [g] is set to [true], the graph of a DP problem is printed. Per default
 [g = false]. *)
 val fprintfm : ?g:bool -> Format.formatter -> t -> unit Rewritingx.Monad.t
 (** [fprintfm ~g:g fmt p] prints [p] using the [OCaml] module [Format]. If
 [g] is set to [true], the graph of a DP problem is printed. Per default
 [g = false]. Function symbols and variables are represented by their names
 registered in the underlying signature. If the name of a function symbol or
 variable is not defined, a randomly generated name is printed. Note that as
 a side effect copies of the underlying signature are changed too. This
 function is not tail-recursive. *)
 val fprintfx : ?g:bool -> t -> Format.formatter -> unit Rewritingx.Monad.t
 (** [fprintfx ~g:g p fmt] prints [p] in XML using the [OCaml] module [Format].
 If [g] is set to [true], the graph of a DP problem is printed. Per default
 [g = false]. Function symbols and variables are represented by their names
 registered in the underlying signature. If the name of a function symbol or
 variable is not defined, a randomly generated name is printed. Note that as
 a side effect copies of the underlying signature are changed too. This
 function is not tail-recursive. *)
 val fprintfx_cm : t -> Format.formatter -> unit Rewritingx.Monad.t
 (** [fprintfx_cm p fmt] prints the complexity measure RC or DC in XML 
  using the [OCaml] module [Format]. Note that as
 a side effect copies of the underlying signature are changed too. *)
 val to_string : ?g:bool -> t -> string
 (** [to_string ~g:g p] returns a string that represents [p]. If [g] is set
 to [true], the graph of a DP problem is printed. Per default [g = false]. *)
 val to_stringm : ?g:bool -> t -> string Rewritingx.Monad.t
 (** [to_stringm ~g:g p] returns a formatted string that represents [p].
 If [g] is set to [true], the graph of a DP problem is printed. Per default
 [g = false]. Function symbols and variables are represented by their names
 registered in the underlying signature. If the name of a function symbol or
 variable is not defined, a randomly generated name is used. Note that as a
 side effect copies of the underlying signature are changed too. This
 function is not tail-recursive. *)
 val to_stringx : ?g:bool -> t -> string Rewritingx.Monad.t
 (** [to_stringx ~g:g p] returns a formatted string in XML that represents
 [p]. If [g] is set to [true], the graph of a DP problem is printed. Per
 default [g = false]. Function symbols and variables are represented by their
 names registered in the underlying signature. If the name of a function symbol
 or variable is not defined, a randomly generated name is used. Note that as a
 side effect copies of the underlying signature are changed too. This function
 is not tail-recursive. *)
end

(** {2 Module Answer} *)

(** Answer
@author Bertram Felgenhauer
@since  Fri Mar 29 12:41:55 CET 2013 *)
module Result : sig
 type t

 (** {3 Constructors and Destructors} *)
 val make_yes : Problem.t list -> t
 val make_no : t

 val yes : t -> Problem.t list
 val no : t -> unit

 (** {3 Predicates} *)
 val is_yes : t -> bool
 val is_no : t -> bool

 (** {3 Utilities} *)
 val get_ops : t -> Problem.t list
end

(** {2 Module Modifier} *)

(** Modifiers
@author Martin Korp
@since  Mon Sep  1 12:22:31 CEST 2009 *)

(** This module provides several techniques which can be used to modify
a termination problem. In difference to transformation techniques, these
methods get additional (history) information. *)
module Modifier : sig
 (** {3 Module Restore} *)
 
 (** Restore TRS
 @author Martin Korp
 @since  Mon Sep  1 12:22:31 CEST 2009 *)
 
 (** This module implements a modifier which restores the TRS of a given
 DP problem. *)
 module Restore : sig
  type t

  (** {4 Globals} *)

  val code : string
  (** [code] defines the shortcut that has to be used to refer to this
  modifier within TTT2. *)
  val help : string * string list * (string * string) list
  (** [help] provides a detailed description of this modifier and its flags. *)

  (** {4 Modifier} *)

  val solve : string list -> Problem.t -> Problem.t -> t option
  (** [solve fs p q] transforms [q] by replacing the underlying TRS with the
  one of [p]. If one of the given problems is not a DP problem, [None] is
  returned.
  @raise Failure if [fs] consists of some unknown flag. *)

  (** {4 Destructors} *)

  val get_ips : t -> Problem.t * Problem.t
  (** [get_ips p] returns the two input problems. *)
  val get_op : t -> Problem.t
  (** [get_op p] returns the resulting DP problem of [p]. *)

  (** {4 Complexity Bounds} *)

  val complexity : Util.Complexity.t -> t -> Util.Complexity.t
  (** [complexity c p] returns information regarding the complexity of the
  new termination problem. *)

  (** {4 Compare Functions} *)

  val equal : t -> t -> bool
  (** [equal p q] checks if the proof [p] is equivalent to [q]. *)

  (** {4 Printers} *)
  
  val fprintf : (Format.formatter -> unit Rewritingx.Monad.t) list
    -> Format.formatter -> t -> unit Rewritingx.Monad.t
  val fprintfx : (Format.formatter -> unit Rewritingx.Monad.t) list
    -> t -> Format.formatter -> unit Rewritingx.Monad.t
 end
end

module type TERMINAL_PROCESSOR = sig
  type t

  val code : string
  (** The name of the processor. *)
  val help : string * string list * (string * string) list
  (** A textual description of the processor and its flags. *)
  val solve : string list -> Problem.t -> t option Rewritingx.Monad.t
  (** [solve fs p] applies the processor with flags [fs] to the problem [p].
  @raise Failure if [fs] consists of some unknown flag. *)
  val get_ip : t -> Problem.t
  (** [get_ip p] returns the input problem of [p]. *)
  val equal : t -> t -> bool
  (** [equal p q] checks if the proof [p] is equivalent to [q]. *)
  val fprintf : (Format.formatter -> unit Rewritingx.Monad.t) list
    -> Format.formatter -> t -> unit Rewritingx.Monad.t
  (** [fprintf fs fmt p] *)
  val fprintfx : (Format.formatter -> unit Rewritingx.Monad.t) list
    -> t -> Format.formatter -> unit Rewritingx.Monad.t
  (** [fprintfx fs p fmt] *)
end

module type PROCESSOR = sig
  include TERMINAL_PROCESSOR
  val get_op : t -> Problem.t
  (** [get_op p] returns the remaining problem of [p]. *)
end

module type DECISION_PROCESSOR = sig
  include TERMINAL_PROCESSOR
  val get_result : t -> Result.t
  (** [get_result] returns the result of the processor *)
end

module type COMPLEXITY_PROCESSOR = sig
  include PROCESSOR
  val complexity : Util.Complexity.t -> t -> Util.Complexity.t
  (** [complexity c p] returns information regarding the complexity of the new
  termination problem. *)
end

(** {2 Module Nontermination} *)

(** Nontermination Techniques
@author Martin Korp, Christian Sternagel, Harald Zankl
@since  Mon Sep  1 12:22:31 CEST 2009 *)

(** This module provides several techniques which can be used to prove that a
certain TRS is nonterminating. *)
module Nontermination : sig
  (** {3 Module Contained} *)
  
  (** Containment Processor
  @author Martin Korp
  @since  Mon Sep  1 12:22:31 CEST 2009 *)
  
  (** This module implements the containment processor which proves
  nontermination of a given TRS by checking whether there exists a rewrite rule
  [l -> r] such that an instance of [l] is a subterm of [r]. *)
  module Contained : TERMINAL_PROCESSOR
 
  (** {3 Module LoopSat} *)
  
  (** Loops for SRSs
  @author Harald Zankl
  @since  Mon May 11 20:03:20 CEST 2009 *)
  
  (** Find Loops (for SRSs) by encoding a looping reduction in SAT *)
  module LoopSat : TERMINAL_PROCESSOR
 
  (** {3 Module Unfolding} *)
  
  (** Loops for SRSs and TRSs
  @author Christian Sternagel
  @since Fri May 15 16:38:52 CEST 2009 *)
  
  (**  Find loops using unfoldings. *)
  module Unfolding : TERMINAL_PROCESSOR
 
  (** {3 Module Variables} *)
  
  (** Fresh Variable Processor
  @author Martin Korp
  @since  Mon Sep  1 12:22:31 CEST 2009 *)
  
  (** This module implements the fresh variable processor which proves
  nontermination of a given TRS by checking whether it fulfills the variable
  condition (i.e., for each rewrite rule [l -> r], [l] is not a variable and
  each variable that occurs in [r] occurs also in [l]).
    For relative termination problems it is checked that there are no
  left-erasing or right-duplicating rules in the relative component.
  (This is a necessary condition for relative termination to be
  found in Geser's PhD thesis.) *)
  module Variables : TERMINAL_PROCESSOR
end

module type PREDICATE = sig
  val code : string
  (** The name of the predicate. *)
  val help : string * string list * (string * string) list
  (** A textual description of the predicate and its flags. *)
  val solve : string list -> Problem.t -> bool Rewritingx.Monad.t
  (** [solve fs p] applies the predicate with flags [fs] to the problem [p].
  @raise Failure if [fs] consists of some unknown flag. *)
end

(** {2 Module Predicate} *)

(** Predicates
@author Martin Korp, Christian Sternagel, Harald Zankl
@since  Mon Sep  1 12:22:31 CEST 2009 *)

(** Predicates on problems. *)
module Predicate : sig
  module Applicative : PREDICATE
  module Collapsing : PREDICATE
  module Constructor : PREDICATE
  module Dummy : PREDICATE
  module Duplicating : PREDICATE
  module Erasing : PREDICATE
  module Flat : PREDICATE
  module Full : PREDICATE
  module Ground : PREDICATE
  module Innermost : PREDICATE
  module LeftGround : PREDICATE
  module LeftLinear : PREDICATE
  module Linear : PREDICATE
  module Overlapping : PREDICATE
  module Overlay : PREDICATE
  module Outermost : PREDICATE
  module Relative : PREDICATE
  module RightGround : PREDICATE
  module RightLinear : PREDICATE
  module Shallow : PREDICATE
  module Srs : PREDICATE
  module Standard : PREDICATE
  module StronglyNonOverlapping : PREDICATE
  module Trs : PREDICATE
  module Wcr : PREDICATE
end

(** {2 Module Termination} *)

(** Termination Techniques
@author Martin Korp, Christian Sternagel, Harald Zankl
@since  Mon Sep  1 12:22:31 CEST 2009 *)

(** This module provides several techniques which can be used to prove
termination of a TRS. *)
module Termination : sig
 (** {3 Module Arctic} *)
 
 (** Arctic Matrix Processor
 @author Harald Zankl
 @since  Mon May 11 12:24:21 CEST 2009 *)
 
 (** This module implements the arctic matrix method. *)
 module Arctic : COMPLEXITY_PROCESSOR

 (** {3 Module Bounds} *)

 (** Match-Bounds
 @author Martin Korp
 @since  Mon Sep  1 12:22:31 CEST 2009 *)
 
 (** This module implements the match-bound technique for TRSs. *)
 module Bounds : COMPLEXITY_PROCESSOR

 (** {3 Module Cfs} *)

 (** Counting function symbols
 @author Sysrah Winkler
 @since  Fri Dec 23 12:22:31 CEST 2011 *)

 (** This module implements simple function symbol counting. *)
 module Cfs : COMPLEXITY_PROCESSOR

 (** {3 Module Dp} *)
 
 (** DP Processor
 @author Martin Korp
 @since  Mon Sep  1 12:22:31 CEST 2009 *)
 
 (** This module implements the dependency pair processor which transforms a
 TRS into the initial DP problem. *)
 module Dp : COMPLEXITY_PROCESSOR

 (** {3 Module Dg} *)

 (** DG Processor
 @author Martin Korp
 @since  Mon Sep  1 12:22:31 CEST 2009 *)
 
 (** This module implements various dependency graph processors. *)
 module Dg : sig
  (** {4 Module Adg} *)

  (** Approximated DG Processor
  @author Martin Korp
  @since  Mon May  5 17:10:46 CEST 2010 *)
  
  (** This module implements a dependency graph processors based on tree
  automata techniques. The approximated dependency graph does not consist
  of an arc from a dependency pair [s] to a dependency pair [t] if no ground
  instance of the right-hand side of [s] can be rewritten to some ground
  instance of the left-hand side of [t] and vice versa. To decide both
  conditions the underlying TRS is approximated. *)
  module Adg : COMPLEXITY_PROCESSOR

  (** {4 Module Cdg} *)

  (** Completion DG Processor
  @author Martin Korp
  @since  Mon Sep  1 12:22:31 CEST 2009 *)
  
  (** This module implements a dependency graph processors based on tree
  automata techniques. The c-dependency graph does not consist of an arc
  from a dependency pair [s] to a dependency pair [t] if a compatible tree
  automaton could be constructed which accepts all ground instances of
  [ren(rhs(s))] but not [lhs(t)]. *)
  module Cdg : COMPLEXITY_PROCESSOR

  (** {4 Module Edg} *)

  (** Estimated DG Processor
  @author Martin Korp
  @since  Mon Sep  1 12:22:31 CEST 2009 *)
  
  (** This module implements the estimated dependency graph processors. The
  estimated dependency graph consists of an arc from a dependency pair [s]
  to a dependency pair [t] if and only if both [tcap(rhs(s),r)] unifies with
  [lhs(t)] and [tcap(lhs(t),rev(r))] unifies with [rhs(t)]. Here [r] denotes
  the TRS of the given DP problem. *)
  module Edg : COMPLEXITY_PROCESSOR

  (** {4 Module Tdg} *)

  (** Trivial DG Processor
  @author Martin Korp
  @since  Mon Sep  1 12:22:31 CEST 2009 *)
  
  (** This module implements a trivial dependency graph processors. The trivial
  dependency graph consists of an arc from a dependency pair [s] to a dependency
  pair [t] if and only if the root symbol of the right-hand side of [s] is equal
  to the root symbol of the left-hand side of [t]. *)
  module Tdg : COMPLEXITY_PROCESSOR
 end

 (** {3 Module KBO} *)
 
 (** KBO Processor
 @author Harald Zankl
 @since  Fri May  1 20:16:08 CEST 2009 *)
 
 (** This module implements the Knuth-Bendix ordering. *)
 module Kbo : COMPLEXITY_PROCESSOR

 (** {3 Module TKBO} *)
 
 (** TKBO Processor
 @author Harald Zankl
 @since  Mon Aug  8 15:32:13 CEST 2011 *)
 
 (** This module implements the transfinite Knuth-Bendix ordering. *)
 module Tkbo : COMPLEXITY_PROCESSOR

 (** {3 Module LPO} *)
 
 (** LPO Processor
 @author Harald Zankl
 @since  Fri May  1 20:16:08 CEST 2009 *)
 
 (** This module implements the lexicographic path ordering. *)
 module Lpo : COMPLEXITY_PROCESSOR

 (** {3 Module Matrix} *)
 
 (** Matrix Processor
 @author Harald Zankl
 @since  Mon Apr 27 09:40:16 CEST 2009 *)
 
 (** This module implements the matrix method. *)
 module Matrix : COMPLEXITY_PROCESSOR

 (** {3 Module Ordinal} *)
 
 (** Ordinal Interpretations Processor
 @author Harald Zankl
 @since  Mon Oct  3 09:34:02 CEST 2011 *)
 
 (** This module implements the ordinal interpretations. *)
 module Ordinal: COMPLEXITY_PROCESSOR

(** {3 Module HigherOrdinal} *)

 (** Higher Ordinal Interpretations Processor
 @author Harald Zankl
 @since  Mon Oct  3 09:34:02 CEST 2011 *)

 (** This module implements higher ordinal interpretations. *)
 module EpsilonZero: COMPLEXITY_PROCESSOR

 (** {3 Module Fbi} *)
 
 (** Fixed bound Elementary Interpretations Processor
 @author Harald Zankl
 @since  Mon Jul 15 11:41:23 CEST 2013 *)
 
 (** This module implements fixed based elementary interpretations. *)
 module Fbi: PROCESSOR 

 (** {3 Module Poly} *)
 
 (** Poly Processor
 @author Harald Zankl
 @since  Tue Dec  8 16:01:29 CET 2009 *)
 
 (** This module implements polynomial interpretations. *)
 module Poly : COMPLEXITY_PROCESSOR

 (** {3 Module Sccs} *)
 
 (** SCC Processor
 @author Martin Korp
 @since  Mon Sep  1 12:22:31 CEST 2009 *)
 
 (** This module implements the strongly connected component processor which
 splits a DP problem into a set of smaller DP problems by using the information
 provided by the dependency graph. *)
 module Sccs : sig
  type t

  (** {4 Globals} *)

  val code : string
  (** [code] defines the shortcut that has to be used to refer to this
  processor within TTT2. *)
  val help : string * string list * (string * string) list
  (** [help] provides a detailed description of this processor and its flags. *)

  (** {4 Processor} *)

  val solve : string list -> Problem.t -> t option
  (** [solve fs p] splits [p] into the corresponding set of DP problems. If
  the processor does not make progress, [None] is returned.
  @raise Failure if [fs] consists of some unknown flag. *)

  (** {4 Destructors} *)

  val get_ip : t -> Problem.t
  (** [get_ip p] returns the initial DP problem of [p]. *)
  val get_ops : t -> Problem.t list
  (** [get_ops p] returns the computed DP problems. *)

  (** {4 Complexity Bounds} *)

  val complexity : Util.Complexity.t -> t -> Util.Complexity.t
  (** [complexity c p] returns information regarding the complexity of the
  new termination problems. *)

  (** {4 Properties} *)

  val is_empty : t -> bool
  (** [is_empty p] checks if the resulting DP problems are empty, i.e., if
  the do not have any dependency pairs or an empty dependency graph. *)

  (** {4 Compare Functions} *)

  val equal : t -> t -> bool
  (** [equal p q] checks if the proof [p] is equivalent to [q]. *)

  (** {4 Printers} *)
  
  val fprintf : ?s:bool -> (Format.formatter -> unit Rewritingx.Monad.t) list
   -> Format.formatter -> t -> unit Rewritingx.Monad.t
  (** [fprintf ~s:s fs fmt p] prints [p] an the corresponding proofs using the
  [OCaml] module [Format]. Function symbols and variables are represented by
  their names registered in the underlying signature. If the name of a function
  symbol or variable is not defined, a randomly generated name is printed. If
  the flag [s] is set to true, some additional status information are printed.
  Per default [s] is false. Note that as a side effect copies of the underlying
  signature are changed too. This function is not tail-recursive. *)
  val fprintfx : (Format.formatter -> unit Rewritingx.Monad.t) list
   -> t -> Format.formatter -> unit Rewritingx.Monad.t
  (** [fprintfx fs p fmt] prints [p] an the corresponding proofs as XML using
  the [OCaml] module [Format]. Function symbols and variables are represented
  by their names registered in the underlying signature. If the name of a
  function symbol or variable is not defined, a randomly generated name is
  printed. Note that as a side effect copies of the underlying signature are
  changed too. This function is not tail-recursive. *)
 end

 (** {3 Module SemanticLabeling} *)
 
 (** Semantic Labeling Processor
 @author Harald Zankl
 @since  Mon Apr 27 09:40:16 CEST 2009 *)
 
 (** This module implements semantic and predictive labeling. *)
 module SemanticLabeling : COMPLEXITY_PROCESSOR

 (** {3 Module SizeChangeTermintion} *)
 
 (** Size-Change Termination Processor (using subterm relation)
 @author Christian Sternagel
 @since  Mon Sep  1 12:22:31 CEST 2009 *)
 
 (** This module implements the size-change termination processor
 (using the subterm relation) which directly shows finiteness of
 a DP problem. *)
 module SizeChangeTermination : COMPLEXITY_PROCESSOR

 (** {3 Module SubtermCriterion} *)
 
 (** Subterm Criterion Processor
 @author Harald Zankl
 @since  Mon Apr 27 09:40:16 CEST 2009 *)
 
 (** This module implements the subterm criterion processor. *)
 module SubtermCriterion : COMPLEXITY_PROCESSOR

 (** {3 Module Trivial} *)
 
 (** Trivial Processor
 @author Harald Zankl
 @since  Thu Dec 16 16:54:21 CET 2010 *)
 
 (** This module implements the trivial processor. *)
 module Trivial : COMPLEXITY_PROCESSOR
end

(** {2 Module Transformation} *)

(** Transformation Techniques
@author Martin Korp, Christian Sternagel, Harald Zankl
@since  Mon Sep  1 12:22:31 CEST 2009 *)

(** This module provides several techniques which can be used to transform
a TRS. In difference to termination and nontermination techniques, these
methods are not able to prove termination or nontermination of a TRS on
their own. *)
module Transformation : sig
 (** {3 Module Commute} *)
 
 (** Commute Transformation
 @author Harald Zankl
 @since  Fri Jan  7 14:32:57 CET 2011 *)
 
 (** Adds rules with symmetric lhs if rule f(x,y) -> f(y,x) is present. *)
 module Commute : PROCESSOR

 (** {3 Module Cp} *)
 
 (** Complexity Transformation
 @author Martin Korp, Harald Zankl
 @since  Mon May 11 20:03:20 CEST 2009 *)
 
 (** This processor transforms a standard termination problem into an initial
 CP problem. *)
 module Cp : COMPLEXITY_PROCESSOR

 (** {3 Module Cr} *)
 
 (** Church Rosser Transformation
 @author Harald Zankl
 @since  Mon Dec 13 13:41:15 CET 2010 *)
 
 (** This processor transforms standard problem into a church rosser
 problem.  *)
 module Cr : PROCESSOR

 (** {3 Module Dpify} *)
 
 (** Dpify Transformation
 @author Christian Sternagel
 @since  Fri Sep 10 15:30:39 CEST 2010 *)
 
 (** This processor marks the root symbols of lhss and rhss as DP symbols.  *)
 module Dpify : COMPLEXITY_PROCESSOR

 (** {3 Module Emb} *)
 
 (** Embedding Transformation
 @author Harald Zankl
 @since  Fri Nov 16 15:30:39 CEST 2012 *)
 
 (** This processor adds the embedding rules.  *)
 module Emb: PROCESSOR 

 (** {3 Module Linear} *)
 
 (** Linearization of TRSs
 @author Martin Korp
 @since  Mon May 11 20:03:20 CEST 2009 *)
 
 (** This processor transforms a given problem by linearizing all left-hand
 sides. *)
 module Linear : COMPLEXITY_PROCESSOR

 (** {3 Module QuasiRootLabeling} *)
 
 (** Quasi Root-Labeling Transformation
 @author Christian Sternagel
 @since Fri Nov 13 16:51:45 CET 2009 *)
 
 (** This processor applies a special version of semantic labeling.*)
 module QuasiRootLabeling : COMPLEXITY_PROCESSOR

 (** {3 Module Reflect} *)
 
 (** Reflection of TRSs
 @author Martin Korp
 @since  Mon May 11 20:03:20 CEST 2009 *)
 
 (** This processor reverses the arguments of the left- and right-hand sides
 of a given problem. *)
 module Reflect : COMPLEXITY_PROCESSOR

 (** {3 Module Reverse} *)
 
 (** Reversal of SRSs
 @author Martin Korp
 @since  Mon May 11 20:03:20 CEST 2009 *)
 
 (** This processor reverses the the left- and right-hand sides of a given
 problem if each left- and right-hand side is a string. *)
 module Reverse : COMPLEXITY_PROCESSOR

 (** {3 Module RootLabeling} *)
 
 (** Root-Labeling Transformation
 @author Christian Sternagel
 @since  Fri Jul 31 14:20:06 CEST 2009 *)
 
 (** This processor applies a special version of semantic labeling (where the
 carrier is fixed to the function symbols). *)
 module RootLabeling : COMPLEXITY_PROCESSOR

 (** {3 Module Rt} *)
 
 (** Relative Termination Transformation
 @author Martin Korp
 @since  Mon May 11 20:03:20 CEST 2009 *)
 
 (** This processor transforms a given standard termination problem into a
 relative termination problem by duplicating the underlying TRS. *)
 module Rt : COMPLEXITY_PROCESSOR

 (** {3 Module Sorted} *)
 
 (** Sortedness Processor
 @author Bertram Felgenhauer, Harald Zankl
 @since  Fri Jan 28 08:57:11 CET 2011 *)
 
 (** This processor transforms a problem into a list of problems by sort
 information. *)
 module Sorted : sig
  type t

  (** {4 Globals} *)

  val code : string
  (** [code] defines the shortcut that has to be used to refer to this
  processor within TTT2. *)
  val help : string * string list * (string * string) list
  (** [help] provides a detailed description of this processor and its flags. *)

  (** {4 Processor} *)

  val solve : string list -> Problem.t -> t option Rewritingx.Monad.t
  (** [solve f p] transforms [p] into a list of problems. *)

  (** {4 Destructors} *)

  val get_ip : t -> Problem.t
  (** [get_ip p] returns the initial problem. *)
  val get_ops : t -> Problem.t list
  (** [get_ops p] returns the resulting problems. *)

  (** {4 Complexity Bounds} *)

  val complexity : Util.Complexity.t -> t -> Util.Complexity.t
  (** [complexity c p] returns information regarding the complexity of the
  new problems. *)

  (** {4 Compare Functions} *)

  val equal : t -> t -> bool
  (** [equal p q] checks if the proof [p] is equivalent to [q]. *)

  (** {4 Printers} *)
  
  val fprintf : (Format.formatter -> unit Rewritingx.Monad.t) list
   -> Format.formatter -> t -> unit Rewritingx.Monad.t
  (** [fprintf fs fmt p] prints [p] an the corresponding proofs using the
  [OCaml] module [Format]. Function symbols and variables are represented
  by their names registered in the underlying signature. If the name of a
  function symbol or variable is not defined, a randomly generated name is
  printed. Note that as a side effect copies of the underlying signature
  are changed too. This function is not tail-recursive. *)
  val fprintfx : (Format.formatter -> unit Rewritingx.Monad.t) list
   -> t -> Format.formatter -> unit Rewritingx.Monad.t
  (** [fprintfx fs p fmt] prints [p] an the corresponding proofs as XML using
  the [OCaml] module [Format]. Function symbols and variables are represented
  by their names registered in the underlying signature. If the name of a
  function symbol or variable is not defined, a randomly generated name is
  printed. Note that as a side effect copies of the underlying signature are
  changed too. This function is not tail-recursive. *)
 end

 (** {3 Module Split} *)
 
 (** Splitting Processor
 @author Martin Korp, Harald Zankl
 @since  Mon May 11 20:03:20 CEST 2009 *)
 
 (** This processor transforms a CP problem into a list of CP problems by
 relating each rewrite rule for which no complexity bound has been proven
 so far with all other rules. *)
 module Split : sig
  type t

  (** {4 Globals} *)

  val code : string
  (** [code] defines the shortcut that has to be used to refer to this
  processor within TTT2. *)
  val help : string * string list * (string * string) list
  (** [help] provides a detailed description of this processor and its flags. *)

  (** {4 Processor} *)

  val generate : string list -> Problem.t -> Problem.t list -> t option
  (** [generate f p ps] transforms [p] into the list of complexity problems
  [ps] if [ps] represents a valid splitting. *)
  val solve : string list -> Problem.t -> t option
  (** [solve f p] transforms [p] into a list of complexity problems. *)

  (** {4 Destructors} *)

  val get_ip : t -> Problem.t
  (** [get_ip p] returns the initial CP problem. *)
  val get_ops : t -> Problem.t list
  (** [get_ops p] returns the resulting CP problems. *)

  (** {4 Complexity Bounds} *)

  val complexity : Util.Complexity.t -> t -> Util.Complexity.t
  (** [complexity c p] returns information regarding the complexity of the
  new CP problems. *)

  (** {4 Compare Functions} *)

  val equal : t -> t -> bool
  (** [equal p q] checks if the proof [p] is equivalent to [q]. *)

  (** {4 Printers} *)
  
  val fprintf : (Format.formatter -> unit Rewritingx.Monad.t) list
   -> Format.formatter -> t -> unit Rewritingx.Monad.t
  (** [fprintf fs fmt p] prints [p] an the corresponding proofs using the
  [OCaml] module [Format]. Function symbols and variables are represented
  by their names registered in the underlying signature. If the name of a
  function symbol or variable is not defined, a randomly generated name is
  printed. Note that as a side effect copies of the underlying signature
  are changed too. This function is not tail-recursive. *)
  val fprintfx : (Format.formatter -> unit Rewritingx.Monad.t) list
   -> t -> Format.formatter -> unit Rewritingx.Monad.t
  (** [fprintfx fs p fmt] prints [p] an the corresponding proofs as XML using
  the [OCaml] module [Format]. Function symbols and variables are represented
  by their names registered in the underlying signature. If the name of a
  function symbol or variable is not defined, a randomly generated name is
  printed. Note that as a side effect copies of the underlying signature are
  changed too. This function is not tail-recursive. *)
 end

 (** {3 Module St} *)
 
 (** Standard Termination Transformation
 @author Martin Korp
 @since  Mon May 11 20:03:20 CEST 2009 *)
 
 (** This processor transforms a given relative termination problem into a
 standard termination problem by taking the union of the the two involved
 TRSs. *)
 module St : COMPLEXITY_PROCESSOR

 (** {3 Module TypeIntroduction} *)
 
 (** Type Introduction
 @author Christian Sternagel
 @since Thu Nov 26 23:05:41 CET 2009 *)
 
 (** This processors introduces types (also called sorts) for a TRS, if
 possible the type information is exploited to split the TRS into
 smaller ones, otherwise the processor fails. *)
 module TypeIntroduction : sig
  type t

  (** {4 Globals} *)

  val code : string
  (** [code] defines the shortcut that has to be used to refer to this
  processor within TTT2. *)
  val help : string * string list * (string * string) list
  (** [help] provides a detailed description of this processor and its flags. *)

  (** {4 Processor} *)

  val solve : string list -> Problem.t -> t option Rewritingx.Monad.t
  (** [solve f p] transforms [p] into a list of problems. *)

  (** {4 Destructors} *)

  val get_ip : t -> Problem.t
  (** [get_ip p] returns the initial problem. *)
  val get_ops : t -> Problem.t list
  (** [get_ops p] returns the resulting problems. *)

  (** {4 Complexity Bounds} *)

  val complexity : Util.Complexity.t -> t -> Util.Complexity.t
  (** [complexity c p] returns information regarding the complexity of the
  new problems. *)

  (** {4 Compare Functions} *)

  val equal : t -> t -> bool
  (** [equal p q] checks if the proof [p] is equivalent to [q]. *)

  (** {4 Printers} *)
  
  val fprintf : (Format.formatter -> unit Rewritingx.Monad.t) list
   -> Format.formatter -> t -> unit Rewritingx.Monad.t
  (** [fprintf fs fmt p] prints [p] an the corresponding proofs using the
  [OCaml] module [Format]. Function symbols and variables are represented
  by their names registered in the underlying signature. If the name of a
  function symbol or variable is not defined, a randomly generated name is
  printed. Note that as a side effect copies of the underlying signature
  are changed too. This function is not tail-recursive. *)
  val fprintfx : (Format.formatter -> unit Rewritingx.Monad.t) list
   -> t -> Format.formatter -> unit Rewritingx.Monad.t
  (** [fprintfx fs p fmt] prints [p] an the corresponding proofs as XML using
  the [OCaml] module [Format]. Function symbols and variables are represented
  by their names registered in the underlying signature. If the name of a
  function symbol or variable is not defined, a randomly generated name is
  printed. Note that as a side effect copies of the underlying signature are
  changed too. This function is not tail-recursive. *)
 end

 (** {3 Module Uncurry} *)
 
 (** Uncurrying
 @author Harald Zankl
 @since  Mon May 11 20:03:20 CEST 2009 *)
 
 (** This processor uncurries a given TRS if it is applicable. *)
 module Uncurry : COMPLEXITY_PROCESSOR

 (** {3 Module Uncurryx} *)
 
 (** Generalized Uncurrying
 @author Christian Sternagel
 @since  Thu Dec  9 09:02:31 CET 2010 *)
 
 (** This processor uncurries a given TRS if it is applicable. *)
 module Uncurryx : COMPLEXITY_PROCESSOR

 (** {3 Module Ur} *)
 
 (** Usable Rules
 @author Martin Korp, Harald Zankl
 @since  Mon May 11 20:03:20 CEST 2009 *)
 
 (** This processor computes the usable rules of a given DP problem. Note
 that per default the processor is not sound if the DP problem is duplicating.
 To ensure soundness you have to set the corresponding flags. *)
 module Ur : COMPLEXITY_PROCESSOR
end

(** {2 Module Confluence} *)

(** Confluence Techniques
@author Martin Korp, Harald Zankl
@since  Sun Dec 26 17:51:21 CET 2010 *)

(** This module provides several techniques which can be used to (dis)prove
confluence of a TRS. *)
module Confluence : sig
 (** {3 Module Closed} *)
 
 (** Closedness Processor
 @author Harald Zankl
 @since  Tue Jan 11 10:37:49 CET 2011 *)
 
 (** This processor checks critical pairs XY closed.  *)
 module Closed : PROCESSOR

 (** {3 Module Nonconfluence} *)
 
 (** Nonconfluence Processor
 @author Martin Korp 
 @since  Sun Dec 26 17:52:34 CET 2010 *)
 
 (** This module implements a non-confluence check based on tree automata. *)
 module Nonconfluence : TERMINAL_PROCESSOR

 (** {3 Module RuleLabeling} *)
 
 (** Rule Labeling Processor
 @author Harald Zankl
 @since  Sun Dec 26 17:58:39 CET 2010 *)
 
 (** This module implements the rule labeling heuristic. *)
 module RuleLabeling : COMPLEXITY_PROCESSOR

 (** {3 Module Shift} *)
 
 (** Shift Processor
 @author Harald Zankl
 @since  Sun Dec 26 17:58:39 CET 2010 *)
 
 (** This module shifts strict rules to weak rules. *)
 module Shift : PROCESSOR

 (** {3 Module Decreasing} *)
 
 (** Decreasing Processor
 @author Harald Zankl
 @since  Wed Dec 29 13:27:27 CET 2010 *)
 
 (** This module drops critical diagrams if they are decreasing. *)
 module Decreasing : COMPLEXITY_PROCESSOR

 (** {3 Module GroundCR} *)
 (** Ground Confluence Processor
 @author Bertram Felgenhauer
 @since  Wed May 25 12:48:17 CEST 2011 *)

 (* This module decides confluence for curried, ground TRSs. *)
 module GroundCR : DECISION_PROCESSOR

 (** AotoToyama
 @author Benjamin Hoeller 
 @since  Tue Mar 21 10:37:49 CET 2012 *)
 
 (** This processor checks confluence by the theorem of Aoto and Toyama.  *)
 module AotoToyama: PROCESSOR

 (** KleinHirokawa
 @author Benjamin Hoeller
 @since  Mon Feb 18 15:26:18 CET 2013 *)

 (** This processor is based on the confluence Criteria of Klein and Hirokawa.*)
 module KleinHirokawa: PROCESSOR

end

(** {3 Module XmlOutput} *)

(** XML Output for Processors
@author Christian Sternagel
@since  Thu May  5 14:27:10 CEST 2011 *)

(** *)
module XmlOutput : sig
 type t = unit Rewritingx.Monad.t

 val id : Format.formatter -> t
 val seq : (Format.formatter -> t) list -> Format.formatter -> t
 val node : string -> (Format.formatter -> t) list -> Format.formatter -> t
 val int : string -> int -> Format.formatter -> t
 val bool : string -> bool -> Format.formatter -> t
 val leaf : string -> Format.formatter -> t
 val string : string -> string -> Format.formatter -> t

end
