;; Statement-only formalization of miniF2F artifact mathd_algebra_149:
        ;; an exact duplicate-free enumeration of the piecewise function's real preimage of 10 has sum 6.
        ;; This file contains no proof.
        ;;
        ;; The operation symbols below present an arbitrary real-closed ordered
        ;; field. Every field, order, rational-embedding, and real-closedness law
        ;; is an explicit premise of the statement. By first-order transfer this
        ;; preserves the source proposition over the real numbers without
        ;; restricting variables to ACL2's executable rationals.

        (in-package "ACL2")

        (set-inhibit-output-lst '(prove proof-tree event summary))

        (defstub m149-real-p (value) t)
(defstub m149-zero () t)
(defstub m149-one () t)
(defstub m149-add (left right) t)
(defstub m149-mul (left right) t)
(defstub m149-neg (value) t)
(defstub m149-inv (value) t)
(defstub m149-lt (left right) t)
(defstub m149-of-rational (value) t)

(defun m149-sub (left right)
  (m149-add left (m149-neg right)))

(defun m149-div (left right)
  (m149-mul left (m149-inv right)))

(defun m149-le (left right)
  (or (equal left right) (m149-lt left right)))

(defun m149-nonnegative-p (value)
  (and (m149-real-p value)
       (m149-le (m149-zero) value)))

(defun m149-positive-p (value)
  (and (m149-real-p value)
       (m149-lt (m149-zero) value)))

(defun m149-abs (value)
  (if (m149-lt value (m149-zero))
      (m149-neg value)
    value))

(defun m149-pow (value exponent)
  (declare (xargs :measure (nfix exponent)))
  (if (zp exponent)
      (m149-one)
    (m149-mul
     value
     (m149-pow value (1- exponent)))))

(defun-sk m149-field-laws-p ()
  (forall (x y z)
    (and
     (m149-real-p (m149-zero))
     (m149-real-p (m149-one))
     (not (equal (m149-zero) (m149-one)))
     (implies
      (m149-real-p x)
      (and
       (m149-real-p (m149-neg x))
       (m149-real-p (m149-inv x))
       (equal (m149-add x (m149-zero)) x)
       (equal (m149-add x (m149-neg x))
              (m149-zero))
       (equal (m149-mul x (m149-one)) x)
       (implies
        (not (equal x (m149-zero)))
        (equal (m149-mul x (m149-inv x))
               (m149-one)))))
     (equal (m149-inv (m149-zero))
            (m149-zero))
     (implies
      (and (m149-real-p x)
           (m149-real-p y))
      (and
       (m149-real-p (m149-add x y))
       (m149-real-p (m149-mul x y))
       (equal (m149-add x y)
              (m149-add y x))
       (equal (m149-mul x y)
              (m149-mul y x))))
     (implies
      (and (m149-real-p x)
           (m149-real-p y)
           (m149-real-p z))
      (and
       (equal (m149-add (m149-add x y) z)
              (m149-add x (m149-add y z)))
       (equal (m149-mul (m149-mul x y) z)
              (m149-mul x (m149-mul y z)))
       (equal (m149-mul x (m149-add y z))
              (m149-add
               (m149-mul x y)
               (m149-mul x z))))))))

(defun-sk m149-order-laws-p ()
  (forall (x y z)
    (implies
     (and (m149-real-p x)
          (m149-real-p y)
          (m149-real-p z))
     (and
      (not (m149-lt x x))
      (or (equal x y)
          (m149-lt x y)
          (m149-lt y x))
      (implies
       (and (m149-lt x y)
            (m149-lt y z))
       (m149-lt x z))
      (implies
       (m149-lt x y)
       (m149-lt
        (m149-add x z)
        (m149-add y z)))
      (implies
       (and (m149-lt (m149-zero) x)
            (m149-lt (m149-zero) y))
       (m149-lt
        (m149-zero)
        (m149-mul x y)))))))

(defun-sk m149-rational-laws-p ()
  (forall (a b)
    (implies
     (and (rationalp a) (rationalp b))
     (and
      (m149-real-p (m149-of-rational a))
      (equal (m149-of-rational 0) (m149-zero))
      (equal (m149-of-rational 1) (m149-one))
      (equal
       (m149-of-rational (+ a b))
       (m149-add
        (m149-of-rational a)
        (m149-of-rational b)))
      (equal
       (m149-of-rational (* a b))
       (m149-mul
        (m149-of-rational a)
        (m149-of-rational b)))
      (equal
       (m149-of-rational (- a))
       (m149-neg (m149-of-rational a)))
      (iff
       (equal a b)
       (equal
        (m149-of-rational a)
        (m149-of-rational b)))
      (iff
       (< a b)
       (m149-lt
        (m149-of-rational a)
        (m149-of-rational b)))))))

(defun m149-polynomial-p (coefficients)
  (if (endp coefficients)
      t
    (and
     (m149-real-p (car coefficients))
     (m149-polynomial-p (cdr coefficients)))))

(defun m149-polynomial-value (coefficients x)
  (if (endp coefficients)
      (m149-zero)
    (m149-add
     (car coefficients)
     (m149-mul
      x
      (m149-polynomial-value
       (cdr coefficients) x)))))

(defun m149-leading-coefficient (coefficients)
  (if (endp (cdr coefficients))
      (car coefficients)
    (m149-leading-coefficient (cdr coefficients))))

(defun m149-odd-degree-p (coefficients)
  (and
   (consp coefficients)
   (consp (cdr coefficients))
   (not
    (equal
     (m149-leading-coefficient coefficients)
     (m149-zero)))
   (equal (mod (1- (len coefficients)) 2) 1)))

(defun-sk m149-square-root-exists-p (x)
  (exists (root)
    (and
     (m149-nonnegative-p root)
     (equal (m149-mul root root) x))))

(defun-sk m149-nonnegative-square-roots-p ()
  (forall (x)
    (implies
     (m149-nonnegative-p x)
     (m149-square-root-exists-p x))))

(defun-sk m149-polynomial-root-exists-p (coefficients)
  (exists (root)
    (and
     (m149-real-p root)
     (equal
      (m149-polynomial-value coefficients root)
      (m149-zero)))))

(defun-sk m149-odd-polynomial-roots-p ()
  (forall (coefficients)
    (implies
     (and
      (true-listp coefficients)
      (m149-polynomial-p coefficients)
      (m149-odd-degree-p coefficients))
     (m149-polynomial-root-exists-p coefficients))))

(defun m149-real-closed-field-p ()
  (and
   (m149-field-laws-p)
   (m149-order-laws-p)
   (m149-rational-laws-p)
   (m149-lt (m149-zero) (m149-one))
   (m149-nonnegative-square-roots-p)
   (m149-odd-polynomial-roots-p)))

(defun m149-principal-square-root-p (root value)
  (and
   (m149-nonnegative-p root)
   (equal (m149-mul root root) value)))

(defchoose m149-sqrt (root) (value)
  (m149-principal-square-root-p root value))

        (defun m149-real-list-p (values)
  (if (endp values)
      (equal values nil)
    (and
     (m149-real-p (car values))
     (m149-real-list-p (cdr values)))))

(defun m149-no-duplicates-p (values)
  (if (endp values)
      t
    (and
     (not (member-equal (car values) (cdr values)))
     (m149-no-duplicates-p (cdr values)))))

(defun m149-source-function (x)
  (if (m149-lt x (m149-of-rational -5))
      (m149-add
       (m149-pow x 2)
       (m149-of-rational 5))
    (m149-sub
     (m149-mul (m149-of-rational 3) x)
     (m149-of-rational 8))))

(defun-sk m149-exact-fiber-p (solutions)
  (forall (x)
    (implies
     (m149-real-p x)
     (iff
      (member-equal x solutions)
      (equal
       (m149-source-function x)
       (m149-of-rational 10))))))

(defun m149-sum (solutions)
  (if (endp solutions)
      (m149-zero)
    (m149-add
     (car solutions)
     (m149-sum (cdr solutions)))))

(defun-sk m149-result-p ()
  (exists (solutions)
    (and
     (true-listp solutions)
     (m149-real-list-p solutions)
     (m149-no-duplicates-p solutions)
     (m149-exact-fiber-p solutions)
     (equal
      (m149-sum solutions)
      (m149-of-rational 6)))))

(defun mathd-algebra-149-statement ()
  (implies
   (m149-real-closed-field-p)
   (m149-result-p)))

        (value-triple :itpeval-statement-checked)
        :q
