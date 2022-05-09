import unittest
from smt_encoding.constraints.function import Function, Sort


class TestFunctionEncoding(unittest.TestCase):
    def test_declare_no_sort_function(self):
        self.assertRaises(ValueError, Function, 'a')

    def test_declare_const(self):
        a = Function('a', Sort.integer)
        self.assertEqual(a.name, 'a', "Function name does not match")
        self.assertEqual(a.arity, 0, "Function arity does not match")
        self.assertEqual(a.type, (Sort.integer,), "Function types do not match")

    def test_declare_function(self):
        f = Function('f', Sort.integer, Sort.boolean, Sort.boolean)
        self.assertEqual(f.name, 'f', "Function name does not match")
        self.assertEqual(f.arity, 2, "Function arity does not match")
        self.assertEqual(f.type, (Sort.integer, Sort.boolean, Sort.boolean), "Function types do not match")


if __name__ == '__main__':
    unittest.main()
