open Alcotest;

let test_hello_with_name = (name, ()) => {
  let greeting = "Hello " ++ name ++ "!";
  let expected = Printf.sprintf("Hello %s!", name);
  check(string, "same string", greeting, expected);
};

let erase_exp_tests = [
  ("can greet Tom", `Quick, test_hello_with_name("Tom")),
  ("can greet John", `Quick, test_hello_with_name("John")),
];

// let () = Alcotest.run("Dummy", [("Greeting", erase_exp_tests)]);
