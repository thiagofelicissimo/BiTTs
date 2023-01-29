open Format
open Term
open Eval
open Value
open Typing

let vcst (str : string) : enve = Val ({head = Symb (str); env = []})

let cst (str : string) : term =
  {
    head = Symb(str);
    spine = []
  }

let var (n : int) : term =
  {
    head = Ix(n);
    spine = []
  }

let meta_app (n : int) (args : term list) : term =
  {
    head = Ix(n);
    spine = List.map (fun t -> {binds = 0; body = t}) args
  }

let pi (t : term) (u : term) : term =
  {
    head = Symb("Pi");
    spine = [
      {binds = 1; body = u};
      {binds = 0; body = t}
      ]
  }

let vpi (v : value) (t : term) (env : env) : value =
  {
    head = Symb("Pi");
    env = [
      Clo({binds = 1; body = t; env = env});
      Val(v)
      ]
  }

let app (t : term) (u : term) : term =
  {
    head = Symb("app");
    spine = [
      {binds = 0; body = u};
      {binds = 0; body = t}
      ]
  }

let abs (t : term) : term =
  {
    head = Symb("abs");
    spine = [
      {binds = 1; body = t}
    ]
  }

let abs' (a : term) (t : term) : term =
  {
    head = Symb("abs'");
    spine = [
      {binds = 1; body = t};
      {binds = 0; body = a}
    ]
  }


let vabs (env : env) (t : term) : enve =
  Val ({
      head = Symb("abs");
      env = [
        Clo(
          {binds = 1;
           body = t;
           env = env}
        )]
    })


let vec (t : term) : term =
  {
    head = Symb("vec");
    spine = [
      {binds = 0; body = t}
    ]
  }

let mk_vec (t : term) : term =
  {
    head = Symb("mk_vec");
    spine = [
      {binds = 0; body = t}
    ]
  }



let zero : term =
  {
    head = Symb("zero");
    spine = []
  }

let succ (t : term) : term =
  {
    head = Symb("succ");
    spine = [
      {binds = 0; body = t}
    ]
  }

let plus (t : term) (u : term) : term =
  {
    head = Symb("plus");
    spine = [
      {binds = 0; body = u};
      {binds = 0; body = t}
    ]
  }

let nat_rec (p : term) (p0 : term) (ps : term) (t : term) : term =
  {
    head = Symb("nat_rec");
    spine = [
      {binds = 0; body = t};
      {binds = 2; body = ps};
      {binds = 0; body = p0};
      {binds = 1; body = p}
    ]
  }

let nat_rec_zero : rew_rule =
  let lhs_spine = [
    {binds = 0; body = zero};
    {binds = 2; body = meta_app 2 [var 0; var 1]};
    {binds = 0; body = var 1};
    {binds = 1; body = meta_app 3 [var 0]}
  ] in
  let rhs = var 1 in
  {
    lhs_spine = lhs_spine;
    rhs = rhs
  }

let nat_rec_succ : rew_rule =
  let lhs_spine = [
    {binds = 0; body = succ (var 0)};
    {binds = 2; body = meta_app 3 [var 0; var 1]};
    {binds = 0; body = var 2};
    {binds = 1; body = meta_app 4 [var 0]}
  ] in
  let rhs =
    meta_app 1 [
      nat_rec (meta_app 4 [var 0]) (var 2) (meta_app 3 [var 0; var 1]) (var 0);
      var 0
    ] in
  {
    lhs_spine = lhs_spine;
    rhs = rhs
  }

let _ =
  rew_map := RewTbl.add "nat_rec" [nat_rec_zero; nat_rec_succ] !rew_map

let beta_rule : rew_rule =
  let x = {
    head = Ix(0);
    spine = []
  } in
  let fx = {
    head = Ix(2);
    spine = [
      {binds = 0; body = x}
    ]
  } in
  let abs = {
    head = Symb("abs");
    spine = [
      {binds = 1; body = fx}
    ]
  } in
  let y = {
    head = Ix(0);
    spine = []
  } in
  let fy = {
    head = Ix(1);
    spine = [
      {
        binds = 0;
        body = {head = Ix(0); spine = []}
      }
    ]
  } in
  {
    lhs_spine = [
      {binds = 0; body = y};
      {binds = 0; body = abs}
    ];
    rhs = fy
  }
let _ =
  rew_map := RewTbl.add "app" [beta_rule] !rew_map

let plus_zero_rule : rew_rule =
  {
    lhs_spine = [
      {binds = 0; body = zero};
      {binds = 0; body = var 0}
    ];
    rhs = var 0
  }

let plus_succ_rule : rew_rule =
  {
    lhs_spine = [
      {binds = 0; body = succ (var 0)};
      {binds = 0; body = var 1}
    ];
    rhs = succ (plus (var 1) (var 0))
  }

let _ =
  rew_map := RewTbl.add "plus" [plus_zero_rule; plus_succ_rule] !rew_map


(* EVAL TESTS *)

let e = [vabs [vcst "a"] (app (var 0) (var 1))]
let t = app (var 0) (abs (var 0))

let v =
  app
    (app
       (abs (abs (app
                 (var 1)
                 (var 0))))
       (abs (var 0)))
    (abs (var 0))


let t2 = abs (plus (var 0) zero) (* \x. x + 0 *)
let u2 = abs (var 0) (* (\y.y) *)
let r2 = equal_val (eval_tm [] t2) (eval_tm [] u2) 0

let t3 = abs (app (abs (var 0)) (var 0)) (* (\f x. f x) (\y.y) *)
let u3 = abs (var 0) (* (\y.y) *)
let r3 = equal_val (eval_tm [] t3) (eval_tm [] u3) 0

let plus' = abs (abs (nat_rec (cst "nat") (var 1) (succ (var 0)) (var 0)))
let t4 = abs (app (app plus' (var 0)) zero) (* \x. x + 0 *)
let u4 = abs (var 0) (* (\y.y) *)
let r4 = equal_val (eval_tm [] t4) (eval_tm [] u4) 0

let t5 = eval_tm [] (app (app plus' (succ (succ (succ zero)))) (succ (succ (succ (succ zero)))))
let u5 = eval_tm [] (plus (succ (succ (succ zero))) (succ (succ (succ (succ zero)))))
let v5 = eval_tm [] (succ (succ (succ (succ (succ (succ (succ zero)))))))
let r5 = equal_val t5 u5 0
let r5' = equal_val t5 v5 0

let t6 = eval_tm [vcst "a"] (app (app plus' (succ (succ (var 0)))) (succ (succ zero)))
let u6 = eval_tm [vcst "a"] (plus (succ (succ (var 0))) (succ (succ zero)))
let r6 = equal_val t6 u6 0


let c_test = eval_ctx 5 [vcst "P"; vcst "A"] [Term(var 0); Term(var 1)]


let mk_lvl n : enve = Val({head = Lvl(n); env = []})

let t7 = read_back_tm 2 @@
  eval_tm [mk_lvl 1; mk_lvl 0] (plus (succ (succ (var 1))) (succ (succ (var 0))))
let u7 = succ (succ (plus (succ (succ (var 1))) (var 0)))
let _ = assert (t7 = u7)

let t7' = read_back_tm 0 @@
  eval_tm [] (abs (abs (plus (succ (succ (var 1))) (succ (succ (var 0))))))
let u7' = abs (abs (succ (succ (plus (succ (succ (var 1))) (var 0)))))
let _ = assert (t7' = u7')


(* ----------------------------------------------- *)
(* -------------- TYPING TESTS ------------------- *)
(* ----------------------------------------------- *)

let _ =
  let prems = [
    {
      ctx = [Term (var 1)];
      mode = Neg;
      boundary = Term(meta_app 1 [var 0])
    };
    {
      ctx = [Term (var 0)];
      mode = Ersd;
      boundary = Term(cst "Type")
    };
    {
      ctx = [];
      mode = Ersd;
      boundary = Term(cst "Type")
    }
  ] in
  let mode = Neg in
  let ty = Term(pi (var 2) (meta_app 2 [var 0])) in
  sign := SignTbl.add "abs" {prems = prems; mode = mode; ty = ty} !sign

let _ =
  let prems = [
    {
      ctx = [];
      mode = Neg;
      boundary = Term(cst "nat")
    };
    {
      ctx = [];
      mode = Neg;
      boundary = Term(cst "nat")
    }
  ] in
  let mode = Pos in
  let ty = Term(cst "nat") in
  sign := SignTbl.add "plus" {prems = prems; mode = mode; ty = ty} !sign

let _ =
  check [] (abs (var 0)) (eval_ty [] @@ T.Term(pi (cst "a") (cst "a"))); (* \x.x <= a -> a *)
  check [] (abs (abs (plus (var 0) (var 1))))
    (eval_ty [] @@ Term(pi (cst "nat") (pi (cst "nat") (cst "nat")))); (* \x y. y + x *)

  Format.printf "%a@." pp_vty
    @@ infer [({head = Lvl(0); env = []}, eval_ty [] @@ Term(cst "nat"))] (plus (var 0) (var 0))

let _ =
  let prems = [
    {
      ctx = [Term (var 1)];
      mode = Pos;
      boundary = Term(meta_app 1 [var 0])
    };
    {
      ctx = [Term (var 0)];
      mode = Ersd;
      boundary = Term(cst "Type")
    };
    {
      ctx = [];
      mode = Pos;
      boundary = Term(cst "Type")
    }
  ] in
  let mode = Pos in
  let ty = Term(pi (var 2) (meta_app 2 [var 0])) in
  sign := SignTbl.add "abs'" {prems = prems; mode = mode; ty = ty} !sign;
  sign := SignTbl.add "nat" {prems = []; mode = Pos; ty = Term(cst "Type")} !sign

let _ =
  Format.printf "%a@." pp_ty
    @@ read_back_ty 0
    @@ infer [] (abs' (cst "nat") (var 0))


let _ =
  let prems = [
    {
      ctx = [];
      mode = Neg;
      boundary = Term(cst "nat")
    }
  ] in
  let ty = Term(vec (var 0)) in
  sign := SignTbl.add "mk_vec" {prems = prems; mode = Pos; ty = ty} !sign;
  let prems = [
    {
      ctx = [];
      mode = Neg;
      boundary = Term(cst "nat")
    }
  ] in
  let ty = Term(cst "nat") in
  sign := SignTbl.add "succ" {prems = prems; mode = Pos; ty = ty} !sign;
  sign := SignTbl.add "zero" {prems = []; mode = Pos; ty = ty} !sign

let _ =
  Format.printf "%a@." pp_ty
    @@ read_back_ty 0
    @@ infer [] (abs' (cst "nat") (mk_vec (plus (succ (var 0)) (succ (var 0)))))

let _ =
  check [] (mk_vec (plus (succ zero) (succ zero))) @@ eval_ty [] @@ T.Term(vec (succ (succ zero)))
