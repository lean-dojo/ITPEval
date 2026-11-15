;; Statement-only formalization of miniF2F artifact aime_1995_p7:
        ;; positive naturals k,m,n, a coprime fraction m/n, and a unit-circle pair satisfying the two source equations must have k+m+n=27.
        ;; This file contains no proof.
        ;;
        ;; The operation symbols below present an arbitrary real-closed ordered
        ;; field. Every field, order, rational-embedding, and real-closedness law
        ;; is an explicit premise of the statement. By first-order transfer this
        ;; preserves the source proposition over the real numbers without
        ;; restricting variables to ACL2's executable rationals.

        (in-package "ACL2")

        (set-inhibit-output-lst '(prove proof-tree event summary))

        (defstub aime95p7-real-p (value) t)
(defstub aime95p7-zero () t)
(defstub aime95p7-one () t)
(defstub aime95p7-add (left right) t)
(defstub aime95p7-mul (left right) t)
(defstub aime95p7-neg (value) t)
(defstub aime95p7-inv (value) t)
(defstub aime95p7-lt (left right) t)
(defstub aime95p7-of-rational (value) t)

(defun aime95p7-sub (left right)
  (aime95p7-add left (aime95p7-neg right)))

(defun aime95p7-div (left right)
  (aime95p7-mul left (aime95p7-inv right)))

(defun aime95p7-le (left right)
  (or (equal left right) (aime95p7-lt left right)))

(defun aime95p7-nonnegative-p (value)
  (and (aime95p7-real-p value)
       (aime95p7-le (aime95p7-zero) value)))

(defun aime95p7-positive-p (value)
  (and (aime95p7-real-p value)
       (aime95p7-lt (aime95p7-zero) value)))

(defun aime95p7-abs (value)
  (if (aime95p7-lt value (aime95p7-zero))
      (aime95p7-neg value)
    value))

(defun aime95p7-pow (value exponent)
  (declare (xargs :measure (nfix exponent)))
  (if (zp exponent)
      (aime95p7-one)
    (aime95p7-mul
     value
     (aime95p7-pow value (1- exponent)))))

(defun-sk aime95p7-field-laws-p ()
  (forall (x y z)
    (and
     (aime95p7-real-p (aime95p7-zero))
     (aime95p7-real-p (aime95p7-one))
     (not (equal (aime95p7-zero) (aime95p7-one)))
     (implies
      (aime95p7-real-p x)
      (and
       (aime95p7-real-p (aime95p7-neg x))
       (aime95p7-real-p (aime95p7-inv x))
       (equal (aime95p7-add x (aime95p7-zero)) x)
       (equal (aime95p7-add x (aime95p7-neg x))
              (aime95p7-zero))
       (equal (aime95p7-mul x (aime95p7-one)) x)
       (implies
        (not (equal x (aime95p7-zero)))
        (equal (aime95p7-mul x (aime95p7-inv x))
               (aime95p7-one)))))
     (equal (aime95p7-inv (aime95p7-zero))
            (aime95p7-zero))
     (implies
      (and (aime95p7-real-p x)
           (aime95p7-real-p y))
      (and
       (aime95p7-real-p (aime95p7-add x y))
       (aime95p7-real-p (aime95p7-mul x y))
       (equal (aime95p7-add x y)
              (aime95p7-add y x))
       (equal (aime95p7-mul x y)
              (aime95p7-mul y x))))
     (implies
      (and (aime95p7-real-p x)
           (aime95p7-real-p y)
           (aime95p7-real-p z))
      (and
       (equal (aime95p7-add (aime95p7-add x y) z)
              (aime95p7-add x (aime95p7-add y z)))
       (equal (aime95p7-mul (aime95p7-mul x y) z)
              (aime95p7-mul x (aime95p7-mul y z)))
       (equal (aime95p7-mul x (aime95p7-add y z))
              (aime95p7-add
               (aime95p7-mul x y)
               (aime95p7-mul x z))))))))

(defun-sk aime95p7-order-laws-p ()
  (forall (x y z)
    (implies
     (and (aime95p7-real-p x)
          (aime95p7-real-p y)
          (aime95p7-real-p z))
     (and
      (not (aime95p7-lt x x))
      (or (equal x y)
          (aime95p7-lt x y)
          (aime95p7-lt y x))
      (implies
       (and (aime95p7-lt x y)
            (aime95p7-lt y z))
       (aime95p7-lt x z))
      (implies
       (aime95p7-lt x y)
       (aime95p7-lt
        (aime95p7-add x z)
        (aime95p7-add y z)))
      (implies
       (and (aime95p7-lt (aime95p7-zero) x)
            (aime95p7-lt (aime95p7-zero) y))
       (aime95p7-lt
        (aime95p7-zero)
        (aime95p7-mul x y)))))))

(defun-sk aime95p7-rational-laws-p ()
  (forall (a b)
    (implies
     (and (rationalp a) (rationalp b))
     (and
      (aime95p7-real-p (aime95p7-of-rational a))
      (equal (aime95p7-of-rational 0) (aime95p7-zero))
      (equal (aime95p7-of-rational 1) (aime95p7-one))
      (equal
       (aime95p7-of-rational (+ a b))
       (aime95p7-add
        (aime95p7-of-rational a)
        (aime95p7-of-rational b)))
      (equal
       (aime95p7-of-rational (* a b))
       (aime95p7-mul
        (aime95p7-of-rational a)
        (aime95p7-of-rational b)))
      (equal
       (aime95p7-of-rational (- a))
       (aime95p7-neg (aime95p7-of-rational a)))
      (iff
       (equal a b)
       (equal
        (aime95p7-of-rational a)
        (aime95p7-of-rational b)))
      (iff
       (< a b)
       (aime95p7-lt
        (aime95p7-of-rational a)
        (aime95p7-of-rational b)))))))

(defun aime95p7-polynomial-p (coefficients)
  (if (endp coefficients)
      t
    (and
     (aime95p7-real-p (car coefficients))
     (aime95p7-polynomial-p (cdr coefficients)))))

(defun aime95p7-polynomial-value (coefficients x)
  (if (endp coefficients)
      (aime95p7-zero)
    (aime95p7-add
     (car coefficients)
     (aime95p7-mul
      x
      (aime95p7-polynomial-value
       (cdr coefficients) x)))))

(defun aime95p7-leading-coefficient (coefficients)
  (if (endp (cdr coefficients))
      (car coefficients)
    (aime95p7-leading-coefficient (cdr coefficients))))

(defun aime95p7-odd-degree-p (coefficients)
  (and
   (consp coefficients)
   (consp (cdr coefficients))
   (not
    (equal
     (aime95p7-leading-coefficient coefficients)
     (aime95p7-zero)))
   (equal (mod (1- (len coefficients)) 2) 1)))

(defun-sk aime95p7-square-root-exists-p (x)
  (exists (root)
    (and
     (aime95p7-nonnegative-p root)
     (equal (aime95p7-mul root root) x))))

(defun-sk aime95p7-nonnegative-square-roots-p ()
  (forall (x)
    (implies
     (aime95p7-nonnegative-p x)
     (aime95p7-square-root-exists-p x))))

(defun-sk aime95p7-polynomial-root-exists-p (coefficients)
  (exists (root)
    (and
     (aime95p7-real-p root)
     (equal
      (aime95p7-polynomial-value coefficients root)
      (aime95p7-zero)))))

(defun-sk aime95p7-odd-polynomial-roots-p ()
  (forall (coefficients)
    (implies
     (and
      (true-listp coefficients)
      (aime95p7-polynomial-p coefficients)
      (aime95p7-odd-degree-p coefficients))
     (aime95p7-polynomial-root-exists-p coefficients))))

(defun aime95p7-real-closed-field-p ()
  (and
   (aime95p7-field-laws-p)
   (aime95p7-order-laws-p)
   (aime95p7-rational-laws-p)
   (aime95p7-lt (aime95p7-zero) (aime95p7-one))
   (aime95p7-nonnegative-square-roots-p)
   (aime95p7-odd-polynomial-roots-p)))

(defun aime95p7-principal-square-root-p (root value)
  (and
   (aime95p7-nonnegative-p root)
   (equal (aime95p7-mul root root) value)))

(defchoose aime95p7-sqrt (root) (value)
  (aime95p7-principal-square-root-p root value))

        (defun aime95p7-gcd (a b)
  (declare (xargs :measure (+ (nfix a) (nfix b))))
  (if (and (natp a) (natp b))
      (cond
       ((equal a 0) b)
       ((equal b 0) a)
       ((< a b)
        (aime95p7-gcd a (- b a)))
       (t
        (aime95p7-gcd (- a b) b)))
    0))

(defun aime95p7-unit-circle-p (sine-t cosine-t)
  (and
   (aime95p7-real-p sine-t)
   (aime95p7-real-p cosine-t)
   (equal
    (aime95p7-add
     (aime95p7-pow sine-t 2)
     (aime95p7-pow cosine-t 2))
    (aime95p7-one))))

(defun aime-1995-p7-statement (k m n sine-t cosine-t)
  (implies
   (and
    (aime95p7-real-closed-field-p)
    (natp k)
    (natp m)
    (natp n)
    (< 0 k)
    (< 0 m)
    (< 0 n)
    (equal (aime95p7-gcd m n) 1)
    (aime95p7-unit-circle-p sine-t cosine-t)
    (equal
     (aime95p7-mul
      (aime95p7-add (aime95p7-one) sine-t)
      (aime95p7-add (aime95p7-one) cosine-t))
     (aime95p7-of-rational 5/4))
    (equal
     (aime95p7-mul
      (aime95p7-sub (aime95p7-one) sine-t)
      (aime95p7-sub (aime95p7-one) cosine-t))
     (aime95p7-sub
      (aime95p7-div
       (aime95p7-of-rational m)
       (aime95p7-of-rational n))
      (aime95p7-sqrt
       (aime95p7-of-rational k)))))
   (equal (+ k m n) 27)))

        (value-triple :itpeval-statement-checked)
        :q
