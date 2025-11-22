open Interp2
open OUnit2

let desugar_tests =
  "desugar test suite" >:::
    [
      "basic test" >:: (fun _ ->
        let prog =
          Option.get
            (parse
               "let id (x : int) : int = x
                let y : int = 5")
        in
        let expected =
          Let
            {
              is_rec = false;
              name = "id";
              ty = FunTy (IntTy, IntTy);
              binding = Fun ("x", IntTy, Var "x");
              body = Let
                       {
                         is_rec = false;
                         name = "y";
                         ty = IntTy;
                         binding = Num 5;
                         body = Var "y";
                       };
            }
        in
        let actual = desugar prog in
        assert_equal expected actual);
      (* TODO: write more tests *)
    ]

let type_of_tests =
  "type_of test suite" >:::
    [
      "basic test" >:: (fun _ ->
        let expr = Fun ("x", BoolTy, Num 5) in
        let expected = Ok (FunTy (BoolTy, IntTy)) in
        let actual = type_of expr in
        assert_equal expected actual
      );
      (* TODO: write more tests *)
    ]

let tests =
  "interp2 test suite" >:::
    [
      desugar_tests;
      type_of_tests;
    ]

let _ = run_test_tt_main tests