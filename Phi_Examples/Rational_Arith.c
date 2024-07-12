
struct Rational {
  int num, den;
};

struct Rational rat_add (struct Rational q1, struct Rational q2) {
  return {
    num: q1.num * q2.den + q2.num * q1.den,
    den: q1.den * q2.den
  };
}

struct Rational rat_sub (struct Rational q1, struct Rational q2) {
  return {
    num: q1.num * q2.den - q2.num * q1.den,
    den: q1.den * q2.den
  };
}

struct Rational rat_mul (struct Rational q1, struct Rational q2) {
  return {
    num: q1.num * q2.num,
    den: q1.den * q2.den
  };
}

struct Rational rat_div (struct Rational q1, struct Rational q2) {
  return {
    num: q1.num * q2.den,
    den: q1.den * q2.num
  };
}

struct Rational rat_lt (struct Rational q1, struct Rational q2) {
  int a = q1.num * q2.den;
  int b = q1.den * q2.num;
  return (q1.den > 0 != q2.den > 0 ? a > b : a < b) ;
}

struct Rational rat_le (struct Rational q1, struct Rational q2) {
  int a = q1.num * q2.den;
  int b = q1.den * q2.num;
  return (q1.den > 0 != q2.den > 0 ? a >= b : a <= b) ;
}

struct Rational rat_gt (struct Rational q1, struct Rational q2) {
  return rat_lt (q2, q1);
}

struct Rational rat_ge (struct Rational q1, struct Rational q2) {
  return rat_le (q2, q1);
}
