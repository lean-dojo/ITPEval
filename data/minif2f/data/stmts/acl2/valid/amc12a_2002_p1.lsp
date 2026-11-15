;; Statement-only formalization of miniF2F artifact amc12a_2002_p1:
        ;; an exact duplicate-free enumeration of the source polynomial's complex zero fiber has sum 7/2.
        ;; This file contains no proof.
        ;;
        ;; The operation symbols below present an arbitrary real-closed ordered
        ;; field. Every field, order, rational-embedding, and real-closedness law
        ;; is an explicit premise of the statement. By first-order transfer this
        ;; preserves the source proposition over the real numbers without
        ;; restricting variables to ACL2's executable rationals.

        (in-package "ACL2")

        (set-inhibit-output-lst '(prove proof-tree event summary))

        (defstub amca02p1-real-p (value) t)
(defstub amca02p1-zero () t)
(defstub amca02p1-one () t)
(defstub amca02p1-add (left right) t)
(defstub amca02p1-mul (left right) t)
(defstub amca02p1-neg (value) t)
(defstub amca02p1-inv (value) t)
(defstub amca02p1-lt (left right) t)
(defstub amca02p1-of-rational (value) t)

(defun amca02p1-sub (left right)
  (amca02p1-add left (amca02p1-neg right)))

(defun amca02p1-div (left right)
  (amca02p1-mul left (amca02p1-inv right)))

(defun amca02p1-le (left right)
  (or (equal left right) (amca02p1-lt left right)))

(defun amca02p1-nonnegative-p (value)
  (and (amca02p1-real-p value)
       (amca02p1-le (amca02p1-zero) value)))

(defun amca02p1-positive-p (value)
  (and (amca02p1-real-p value)
       (amca02p1-lt (amca02p1-zero) value)))

(defun amca02p1-abs (value)
  (if (amca02p1-lt value (amca02p1-zero))
      (amca02p1-neg value)
    value))

(defun amca02p1-pow (value exponent)
  (declare (xargs :measure (nfix exponent)))
  (if (zp exponent)
      (amca02p1-one)
    (amca02p1-mul
     value
     (amca02p1-pow value (1- exponent)))))

(defun-sk amca02p1-field-laws-p ()
  (forall (x y z)
    (and
     (amca02p1-real-p (amca02p1-zero))
     (amca02p1-real-p (amca02p1-one))
     (not (equal (amca02p1-zero) (amca02p1-one)))
     (implies
      (amca02p1-real-p x)
      (and
       (amca02p1-real-p (amca02p1-neg x))
       (amca02p1-real-p (amca02p1-inv x))
       (equal (amca02p1-add x (amca02p1-zero)) x)
       (equal (amca02p1-add x (amca02p1-neg x))
              (amca02p1-zero))
       (equal (amca02p1-mul x (amca02p1-one)) x)
       (implies
        (not (equal x (amca02p1-zero)))
        (equal (amca02p1-mul x (amca02p1-inv x))
               (amca02p1-one)))))
     (equal (amca02p1-inv (amca02p1-zero))
            (amca02p1-zero))
     (implies
      (and (amca02p1-real-p x)
           (amca02p1-real-p y))
      (and
       (amca02p1-real-p (amca02p1-add x y))
       (amca02p1-real-p (amca02p1-mul x y))
       (equal (amca02p1-add x y)
              (amca02p1-add y x))
       (equal (amca02p1-mul x y)
              (amca02p1-mul y x))))
     (implies
      (and (amca02p1-real-p x)
           (amca02p1-real-p y)
           (amca02p1-real-p z))
      (and
       (equal (amca02p1-add (amca02p1-add x y) z)
              (amca02p1-add x (amca02p1-add y z)))
       (equal (amca02p1-mul (amca02p1-mul x y) z)
              (amca02p1-mul x (amca02p1-mul y z)))
       (equal (amca02p1-mul x (amca02p1-add y z))
              (amca02p1-add
               (amca02p1-mul x y)
               (amca02p1-mul x z))))))))

(defun-sk amca02p1-order-laws-p ()
  (forall (x y z)
    (implies
     (and (amca02p1-real-p x)
          (amca02p1-real-p y)
          (amca02p1-real-p z))
     (and
      (not (amca02p1-lt x x))
      (or (equal x y)
          (amca02p1-lt x y)
          (amca02p1-lt y x))
      (implies
       (and (amca02p1-lt x y)
            (amca02p1-lt y z))
       (amca02p1-lt x z))
      (implies
       (amca02p1-lt x y)
       (amca02p1-lt
        (amca02p1-add x z)
        (amca02p1-add y z)))
      (implies
       (and (amca02p1-lt (amca02p1-zero) x)
            (amca02p1-lt (amca02p1-zero) y))
       (amca02p1-lt
        (amca02p1-zero)
        (amca02p1-mul x y)))))))

(defun-sk amca02p1-rational-laws-p ()
  (forall (a b)
    (implies
     (and (rationalp a) (rationalp b))
     (and
      (amca02p1-real-p (amca02p1-of-rational a))
      (equal (amca02p1-of-rational 0) (amca02p1-zero))
      (equal (amca02p1-of-rational 1) (amca02p1-one))
      (equal
       (amca02p1-of-rational (+ a b))
       (amca02p1-add
        (amca02p1-of-rational a)
        (amca02p1-of-rational b)))
      (equal
       (amca02p1-of-rational (* a b))
       (amca02p1-mul
        (amca02p1-of-rational a)
        (amca02p1-of-rational b)))
      (equal
       (amca02p1-of-rational (- a))
       (amca02p1-neg (amca02p1-of-rational a)))
      (iff
       (equal a b)
       (equal
        (amca02p1-of-rational a)
        (amca02p1-of-rational b)))
      (iff
       (< a b)
       (amca02p1-lt
        (amca02p1-of-rational a)
        (amca02p1-of-rational b)))))))

(defun amca02p1-polynomial-p (coefficients)
  (if (endp coefficients)
      t
    (and
     (amca02p1-real-p (car coefficients))
     (amca02p1-polynomial-p (cdr coefficients)))))

(defun amca02p1-polynomial-value (coefficients x)
  (if (endp coefficients)
      (amca02p1-zero)
    (amca02p1-add
     (car coefficients)
     (amca02p1-mul
      x
      (amca02p1-polynomial-value
       (cdr coefficients) x)))))

(defun amca02p1-leading-coefficient (coefficients)
  (if (endp (cdr coefficients))
      (car coefficients)
    (amca02p1-leading-coefficient (cdr coefficients))))

(defun amca02p1-odd-degree-p (coefficients)
  (and
   (consp coefficients)
   (consp (cdr coefficients))
   (not
    (equal
     (amca02p1-leading-coefficient coefficients)
     (amca02p1-zero)))
   (equal (mod (1- (len coefficients)) 2) 1)))

(defun-sk amca02p1-square-root-exists-p (x)
  (exists (root)
    (and
     (amca02p1-nonnegative-p root)
     (equal (amca02p1-mul root root) x))))

(defun-sk amca02p1-nonnegative-square-roots-p ()
  (forall (x)
    (implies
     (amca02p1-nonnegative-p x)
     (amca02p1-square-root-exists-p x))))

(defun-sk amca02p1-polynomial-root-exists-p (coefficients)
  (exists (root)
    (and
     (amca02p1-real-p root)
     (equal
      (amca02p1-polynomial-value coefficients root)
      (amca02p1-zero)))))

(defun-sk amca02p1-odd-polynomial-roots-p ()
  (forall (coefficients)
    (implies
     (and
      (true-listp coefficients)
      (amca02p1-polynomial-p coefficients)
      (amca02p1-odd-degree-p coefficients))
     (amca02p1-polynomial-root-exists-p coefficients))))

(defun amca02p1-real-closed-field-p ()
  (and
   (amca02p1-field-laws-p)
   (amca02p1-order-laws-p)
   (amca02p1-rational-laws-p)
   (amca02p1-lt (amca02p1-zero) (amca02p1-one))
   (amca02p1-nonnegative-square-roots-p)
   (amca02p1-odd-polynomial-roots-p)))

(defun amca02p1-principal-square-root-p (root value)
  (and
   (amca02p1-nonnegative-p root)
   (equal (amca02p1-mul root root) value)))

(defchoose amca02p1-sqrt (root) (value)
  (amca02p1-principal-square-root-p root value))

(defun amca02p1-complex-p (value)
  (and (consp value)
       (amca02p1-real-p (car value))
       (amca02p1-real-p (cdr value))))

(defun amca02p1-complex (real imaginary)
  (cons real imaginary))

(defun amca02p1-complex-zero ()
  (amca02p1-complex (amca02p1-zero) (amca02p1-zero)))

(defun amca02p1-complex-of-rational (value)
  (amca02p1-complex
   (amca02p1-of-rational value)
   (amca02p1-zero)))

(defun amca02p1-complex-add (left right)
  (amca02p1-complex
   (amca02p1-add (car left) (car right))
   (amca02p1-add (cdr left) (cdr right))))

(defun amca02p1-complex-neg (value)
  (amca02p1-complex
   (amca02p1-neg (car value))
   (amca02p1-neg (cdr value))))

(defun amca02p1-complex-sub (left right)
  (amca02p1-complex-add left (amca02p1-complex-neg right)))

(defun amca02p1-complex-mul (left right)
  (amca02p1-complex
   (amca02p1-sub
    (amca02p1-mul (car left) (car right))
    (amca02p1-mul (cdr left) (cdr right)))
   (amca02p1-add
    (amca02p1-mul (car left) (cdr right))
    (amca02p1-mul (cdr left) (car right)))))

(defun amca02p1-complex-norm-square (value)
  (amca02p1-add
   (amca02p1-mul (car value) (car value))
   (amca02p1-mul (cdr value) (cdr value))))

(defun amca02p1-complex-inv (value)
  (let ((denominator
         (amca02p1-complex-norm-square value)))
    (amca02p1-complex
     (amca02p1-div (car value) denominator)
     (amca02p1-neg
      (amca02p1-div (cdr value) denominator)))))

(defun amca02p1-complex-div (left right)
  (amca02p1-complex-mul left (amca02p1-complex-inv right)))

(defun amca02p1-complex-pow (value exponent)
  (declare (xargs :measure (nfix exponent)))
  (if (zp exponent)
      (amca02p1-complex-of-rational 1)
    (amca02p1-complex-mul
     value
     (amca02p1-complex-pow value (1- exponent)))))

(defun amca02p1-complex-norm (value)
  (amca02p1-sqrt (amca02p1-complex-norm-square value)))

        (defun amca02p1-complex-list-p (values)
  (if (endp values)
      (equal values nil)
    (and
     (amca02p1-complex-p (car values))
     (amca02p1-complex-list-p (cdr values)))))

(defun amca02p1-no-duplicates-p (values)
  (if (endp values)
      t
    (and
     (not (member-equal (car values) (cdr values)))
     (amca02p1-no-duplicates-p (cdr values)))))

(defun amca02p1-source-function (x)
  (let ((linear
         (amca02p1-complex-add
          (amca02p1-complex-mul
           (amca02p1-complex-of-rational 2) x)
          (amca02p1-complex-of-rational 3))))
    (amca02p1-complex-add
     (amca02p1-complex-mul
      linear
      (amca02p1-complex-sub
       x
       (amca02p1-complex-of-rational 4)))
     (amca02p1-complex-mul
      linear
      (amca02p1-complex-sub
       x
       (amca02p1-complex-of-rational 6))))))

(defun-sk amca02p1-exact-fiber-p (solutions)
  (forall (x)
    (implies
     (amca02p1-complex-p x)
     (iff
      (member-equal x solutions)
      (equal
       (amca02p1-source-function x)
       (amca02p1-complex-zero))))))

(defun amca02p1-sum (solutions)
  (if (endp solutions)
      (amca02p1-complex-zero)
    (amca02p1-complex-add
     (car solutions)
     (amca02p1-sum (cdr solutions)))))

(defun-sk amca02p1-result-p ()
  (exists (solutions)
    (and
     (true-listp solutions)
     (amca02p1-complex-list-p solutions)
     (amca02p1-no-duplicates-p solutions)
     (amca02p1-exact-fiber-p solutions)
     (equal
      (amca02p1-sum solutions)
      (amca02p1-complex-of-rational 7/2)))))

(defun amc12a-2002-p1-statement ()
  (implies
   (amca02p1-real-closed-field-p)
   (amca02p1-result-p)))

        (value-triple :itpeval-statement-checked)
        :q
