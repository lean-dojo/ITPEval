;; Statement-only formalization of miniF2F artifact mathd_algebra_80:
        ;; a real x other than -1 satisfying (x-9)/(x+1)=2 equals -11.
        ;; This file contains no proof.
        ;;
        ;; The operation symbols below present an arbitrary real-closed ordered
        ;; field. Every field, order, rational-embedding, and real-closedness law
        ;; is an explicit premise of the statement. By first-order transfer this
        ;; preserves the source proposition over the real numbers without
        ;; restricting variables to ACL2's executable rationals.

        (in-package "ACL2")

        (set-inhibit-output-lst '(prove proof-tree event summary))

        (defstub m80-real-p (value) t)
(defstub m80-zero () t)
(defstub m80-one () t)
(defstub m80-add (left right) t)
(defstub m80-mul (left right) t)
(defstub m80-neg (value) t)
(defstub m80-inv (value) t)
(defstub m80-lt (left right) t)
(defstub m80-of-rational (value) t)

(defun m80-sub (left right)
  (m80-add left (m80-neg right)))

(defun m80-div (left right)
  (m80-mul left (m80-inv right)))

(defun m80-le (left right)
  (or (equal left right) (m80-lt left right)))

(defun m80-nonnegative-p (value)
  (and (m80-real-p value)
       (m80-le (m80-zero) value)))

(defun m80-positive-p (value)
  (and (m80-real-p value)
       (m80-lt (m80-zero) value)))

(defun m80-abs (value)
  (if (m80-lt value (m80-zero))
      (m80-neg value)
    value))

(defun m80-pow (value exponent)
  (declare (xargs :measure (nfix exponent)))
  (if (zp exponent)
      (m80-one)
    (m80-mul
     value
     (m80-pow value (1- exponent)))))

(defun-sk m80-field-laws-p ()
  (forall (x y z)
    (and
     (m80-real-p (m80-zero))
     (m80-real-p (m80-one))
     (not (equal (m80-zero) (m80-one)))
     (implies
      (m80-real-p x)
      (and
       (m80-real-p (m80-neg x))
       (m80-real-p (m80-inv x))
       (equal (m80-add x (m80-zero)) x)
       (equal (m80-add x (m80-neg x))
              (m80-zero))
       (equal (m80-mul x (m80-one)) x)
       (implies
        (not (equal x (m80-zero)))
        (equal (m80-mul x (m80-inv x))
               (m80-one)))))
     (equal (m80-inv (m80-zero))
            (m80-zero))
     (implies
      (and (m80-real-p x)
           (m80-real-p y))
      (and
       (m80-real-p (m80-add x y))
       (m80-real-p (m80-mul x y))
       (equal (m80-add x y)
              (m80-add y x))
       (equal (m80-mul x y)
              (m80-mul y x))))
     (implies
      (and (m80-real-p x)
           (m80-real-p y)
           (m80-real-p z))
      (and
       (equal (m80-add (m80-add x y) z)
              (m80-add x (m80-add y z)))
       (equal (m80-mul (m80-mul x y) z)
              (m80-mul x (m80-mul y z)))
       (equal (m80-mul x (m80-add y z))
              (m80-add
               (m80-mul x y)
               (m80-mul x z))))))))

(defun-sk m80-order-laws-p ()
  (forall (x y z)
    (implies
     (and (m80-real-p x)
          (m80-real-p y)
          (m80-real-p z))
     (and
      (not (m80-lt x x))
      (or (equal x y)
          (m80-lt x y)
          (m80-lt y x))
      (implies
       (and (m80-lt x y)
            (m80-lt y z))
       (m80-lt x z))
      (implies
       (m80-lt x y)
       (m80-lt
        (m80-add x z)
        (m80-add y z)))
      (implies
       (and (m80-lt (m80-zero) x)
            (m80-lt (m80-zero) y))
       (m80-lt
        (m80-zero)
        (m80-mul x y)))))))

(defun-sk m80-rational-laws-p ()
  (forall (a b)
    (implies
     (and (rationalp a) (rationalp b))
     (and
      (m80-real-p (m80-of-rational a))
      (equal (m80-of-rational 0) (m80-zero))
      (equal (m80-of-rational 1) (m80-one))
      (equal
       (m80-of-rational (+ a b))
       (m80-add
        (m80-of-rational a)
        (m80-of-rational b)))
      (equal
       (m80-of-rational (* a b))
       (m80-mul
        (m80-of-rational a)
        (m80-of-rational b)))
      (equal
       (m80-of-rational (- a))
       (m80-neg (m80-of-rational a)))
      (iff
       (equal a b)
       (equal
        (m80-of-rational a)
        (m80-of-rational b)))
      (iff
       (< a b)
       (m80-lt
        (m80-of-rational a)
        (m80-of-rational b)))))))

(defun m80-polynomial-p (coefficients)
  (if (endp coefficients)
      t
    (and
     (m80-real-p (car coefficients))
     (m80-polynomial-p (cdr coefficients)))))

(defun m80-polynomial-value (coefficients x)
  (if (endp coefficients)
      (m80-zero)
    (m80-add
     (car coefficients)
     (m80-mul
      x
      (m80-polynomial-value
       (cdr coefficients) x)))))

(defun m80-leading-coefficient (coefficients)
  (if (endp (cdr coefficients))
      (car coefficients)
    (m80-leading-coefficient (cdr coefficients))))

(defun m80-odd-degree-p (coefficients)
  (and
   (consp coefficients)
   (consp (cdr coefficients))
   (not
    (equal
     (m80-leading-coefficient coefficients)
     (m80-zero)))
   (equal (mod (1- (len coefficients)) 2) 1)))

(defun-sk m80-square-root-exists-p (x)
  (exists (root)
    (and
     (m80-nonnegative-p root)
     (equal (m80-mul root root) x))))

(defun-sk m80-nonnegative-square-roots-p ()
  (forall (x)
    (implies
     (m80-nonnegative-p x)
     (m80-square-root-exists-p x))))

(defun-sk m80-polynomial-root-exists-p (coefficients)
  (exists (root)
    (and
     (m80-real-p root)
     (equal
      (m80-polynomial-value coefficients root)
      (m80-zero)))))

(defun-sk m80-odd-polynomial-roots-p ()
  (forall (coefficients)
    (implies
     (and
      (true-listp coefficients)
      (m80-polynomial-p coefficients)
      (m80-odd-degree-p coefficients))
     (m80-polynomial-root-exists-p coefficients))))

(defun m80-real-closed-field-p ()
  (and
   (m80-field-laws-p)
   (m80-order-laws-p)
   (m80-rational-laws-p)
   (m80-lt (m80-zero) (m80-one))
   (m80-nonnegative-square-roots-p)
   (m80-odd-polynomial-roots-p)))

(defun m80-principal-square-root-p (root value)
  (and
   (m80-nonnegative-p root)
   (equal (m80-mul root root) value)))

(defchoose m80-sqrt (root) (value)
  (m80-principal-square-root-p root value))

        (defun mathd-algebra-80-statement (x)
  (implies
   (and
    (m80-real-closed-field-p)
    (m80-real-p x)
    (not (equal x (m80-of-rational -1)))
    (equal
     (m80-div
      (m80-sub x (m80-of-rational 9))
      (m80-add x (m80-one)))
     (m80-of-rational 2)))
   (equal x (m80-of-rational -11))))

        (value-triple :itpeval-statement-checked)
        :q
