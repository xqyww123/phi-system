
struct Rational {
  int num, den;
} ;

struct Rational rat_add (struct Rational q1, struct Rational q2) {
  return { num: q1.num * q2.den + q2.num * q1.den,
           den: q1.den * q2.den };
}

struct Rational rat_sub (struct Rational q1, struct Rational q2) {
  return { num: q1.num * q2.den - q2.num * q1.den,
           den: q1.den * q2.den };
}

struct Rational rat_mul (struct Rational q1, struct Rational q2) {
  return { num: q1.num * q2.num,
           den: q1.den * q2.den };
}

struct Rational rat_div (struct Rational q1, struct Rational q2) {
  return { num: q1.num * q2.den,
           den: q1.den * q2.num };
}

