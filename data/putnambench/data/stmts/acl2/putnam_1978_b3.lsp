;; Statement-only formalization of PutnamBench corpus artifact putnam_1978_b3:
;; recursively defined real polynomials have largest roots forming a strictly
;; increasing sequence that converges to zero. This file contains no proof.

(in-package "ACL2")

(set-inhibit-output-lst '(prove proof-tree event summary))

;; Scalars are represented in an arbitrary real closed ordered field.
;; Polynomials are canonical coefficient lists in ascending degree order, and
;; the source functions P and a are retained as unbounded tame function
;; objects. Real closed ordered fields agree on the algebraic and order facts
;; used here, and every root of these recursively determined rational
;; polynomials is algebraic over the prime field. Quantifying convergence over
;; positive rational tolerances is equivalent over the reals to quantifying
;; over all positive real tolerances because the positive rationals are cofinal
;; at zero. Thus no real value, sequence entry, or index range is replaced by a
;; finite or rational approximation.

(defun putnam-1978-b3-add (add left right)
  (apply$ add (list left right)))

(defun putnam-1978-b3-mul (mul left right)
  (apply$ mul (list left right)))

(defun putnam-1978-b3-neg (neg value)
  (apply$ neg (list value)))

(defun putnam-1978-b3-inv (inv value)
  (apply$ inv (list value)))

(defun putnam-1978-b3-lt (lt left right)
  (if (apply$ lt (list left right)) t nil))

(defun putnam-1978-b3-le (lt left right)
  (not (putnam-1978-b3-lt lt right left)))

(defun putnam-1978-b3-field-natural (n zero one add)
  (declare (xargs :measure (nfix n)))
  (if (zp n)
      zero
    (putnam-1978-b3-add
     add
     one
     (putnam-1978-b3-field-natural
      (- n 1) zero one add))))

(defun putnam-1978-b3-field-rational
    (value zero one add mul neg inv)
  (if (rationalp value)
      (let* ((magnitude (abs (numerator value)))
             (numerator-value
              (putnam-1978-b3-field-natural
               magnitude zero one add))
             (denominator-value
              (putnam-1978-b3-field-natural
               (denominator value) zero one add))
             (positive-value
              (putnam-1978-b3-mul
               mul
               numerator-value
               (putnam-1978-b3-inv
                inv denominator-value))))
        (if (< value 0)
            (putnam-1978-b3-neg neg positive-value)
          positive-value))
    zero))

(defun putnam-1978-b3-polynomial-coefficients-p
    (coefficients carrier)
  (if (consp coefficients)
      (and
       (apply$ carrier (list (car coefficients)))
       (putnam-1978-b3-polynomial-coefficients-p
        (cdr coefficients) carrier))
    (equal coefficients nil)))

(defun putnam-1978-b3-polynomial-p
    (coefficients carrier zero)
  (and
   (true-listp coefficients)
   (consp coefficients)
   (putnam-1978-b3-polynomial-coefficients-p
    coefficients carrier)
   (or
    (equal (len coefficients) 1)
    (not (equal (car (last coefficients)) zero)))))

(defun putnam-1978-b3-polynomial-normalize (coefficients zero)
  (if (consp coefficients)
      (let ((rest
             (putnam-1978-b3-polynomial-normalize
              (cdr coefficients) zero)))
        (if (and (endp rest)
                 (equal (car coefficients) zero))
            nil
          (cons (car coefficients) rest)))
    nil))

(defun putnam-1978-b3-polynomial-add-raw
    (left right add)
  (cond
   ((endp left) right)
   ((endp right) left)
   (t
    (cons
     (putnam-1978-b3-add add (car left) (car right))
     (putnam-1978-b3-polynomial-add-raw
      (cdr left) (cdr right) add)))))

(defun putnam-1978-b3-polynomial-add
    (left right zero add)
  (let ((sum
         (putnam-1978-b3-polynomial-normalize
          (putnam-1978-b3-polynomial-add-raw
           left right add)
          zero)))
    (if (endp sum)
        (list zero)
      sum)))

(defun putnam-1978-b3-polynomial-scale-raw
    (scalar coefficients mul)
  (if (consp coefficients)
      (cons
       (putnam-1978-b3-mul
        mul scalar (car coefficients))
       (putnam-1978-b3-polynomial-scale-raw
        scalar (cdr coefficients) mul))
    nil))

(defun putnam-1978-b3-polynomial-scale
    (scalar coefficients zero mul)
  (let ((product
         (putnam-1978-b3-polynomial-normalize
          (putnam-1978-b3-polynomial-scale-raw
           scalar coefficients mul)
          zero)))
    (if (endp product)
        (list zero)
      product)))

(defun putnam-1978-b3-polynomial-x-scale
    (scalar coefficients zero mul)
  (cons
   zero
   (putnam-1978-b3-polynomial-scale
    scalar coefficients zero mul)))

(defun putnam-1978-b3-polynomial-eval
    (coefficients x zero add mul)
  (if (endp coefficients)
      zero
    (putnam-1978-b3-add
     add
     (car coefficients)
     (putnam-1978-b3-mul
      mul
      x
      (putnam-1978-b3-polynomial-eval
       (cdr coefficients) x zero add mul)))))

(defun-sk putnam-1978-b3-field-laws-p
    (carrier zero one add mul neg inv)
  (forall
   (x y z)
   (implies
    (and
     (apply$ carrier (list x))
     (apply$ carrier (list y))
     (apply$ carrier (list z)))
    (and
     (apply$ carrier
             (list (putnam-1978-b3-add add x y)))
     (apply$ carrier
             (list (putnam-1978-b3-mul mul x y)))
     (apply$ carrier
             (list (putnam-1978-b3-neg neg x)))
     (apply$ carrier
             (list (putnam-1978-b3-inv inv x)))
     (equal
      (putnam-1978-b3-add
       add (putnam-1978-b3-add add x y) z)
      (putnam-1978-b3-add
       add x (putnam-1978-b3-add add y z)))
     (equal
      (putnam-1978-b3-mul
       mul (putnam-1978-b3-mul mul x y) z)
      (putnam-1978-b3-mul
       mul x (putnam-1978-b3-mul mul y z)))
     (equal
      (putnam-1978-b3-add add x y)
      (putnam-1978-b3-add add y x))
     (equal
      (putnam-1978-b3-mul mul x y)
      (putnam-1978-b3-mul mul y x))
     (equal (putnam-1978-b3-add add x zero) x)
     (equal
      (putnam-1978-b3-add
       add x (putnam-1978-b3-neg neg x))
      zero)
     (equal (putnam-1978-b3-mul mul x one) x)
     (implies
      (equal x zero)
      (equal (putnam-1978-b3-inv inv x) zero))
     (implies
      (not (equal x zero))
      (equal
       (putnam-1978-b3-mul
        mul x (putnam-1978-b3-inv inv x))
       one))
     (equal
      (putnam-1978-b3-mul
       mul x (putnam-1978-b3-add add y z))
      (putnam-1978-b3-add
       add
       (putnam-1978-b3-mul mul x y)
       (putnam-1978-b3-mul mul x z)))))))

(defun-sk putnam-1978-b3-order-laws-p
    (carrier zero add mul lt)
  (forall
   (x y z)
   (implies
    (and
     (apply$ carrier (list x))
     (apply$ carrier (list y))
     (apply$ carrier (list z)))
    (and
     (not (putnam-1978-b3-lt lt x x))
     (or
      (putnam-1978-b3-lt lt x y)
      (equal x y)
      (putnam-1978-b3-lt lt y x))
     (implies
      (and
       (putnam-1978-b3-lt lt x y)
       (putnam-1978-b3-lt lt y z))
      (putnam-1978-b3-lt lt x z))
     (implies
      (putnam-1978-b3-lt lt x y)
      (putnam-1978-b3-lt
       lt
       (putnam-1978-b3-add add x z)
       (putnam-1978-b3-add add y z)))
     (implies
      (and
       (putnam-1978-b3-lt lt zero x)
       (putnam-1978-b3-lt lt zero y))
      (putnam-1978-b3-lt
       lt zero (putnam-1978-b3-mul mul x y)))))))

(defun-sk putnam-1978-b3-square-root-laws-p
    (carrier zero mul lt square-root)
  (forall
   x
   (implies
    (and
     (apply$ carrier (list x))
     (not (putnam-1978-b3-lt lt x zero)))
    (let ((root (apply$ square-root (list x))))
      (and
       (apply$ carrier (list root))
       (not (putnam-1978-b3-lt lt root zero))
       (equal
        (putnam-1978-b3-mul mul root root)
        x))))))

(defun-sk putnam-1978-b3-odd-root-laws-p
    (carrier zero add mul odd-root)
  (forall
   coefficients
   (implies
    (and
     (putnam-1978-b3-polynomial-p
      coefficients carrier zero)
     (evenp (len coefficients)))
    (let ((root (apply$ odd-root (list coefficients))))
      (and
       (apply$ carrier (list root))
       (equal
        (putnam-1978-b3-polynomial-eval
         coefficients root zero add mul)
        zero))))))

(defun putnam-1978-b3-real-closed-field-p
    (carrier zero one add mul neg inv lt square-root odd-root)
  (and
   (tamep-functionp carrier)
   (tamep-functionp add)
   (tamep-functionp mul)
   (tamep-functionp neg)
   (tamep-functionp inv)
   (tamep-functionp lt)
   (tamep-functionp square-root)
   (tamep-functionp odd-root)
   (apply$ carrier (list zero))
   (apply$ carrier (list one))
   (not (equal zero one))
   (putnam-1978-b3-field-laws-p
    carrier zero one add mul neg inv)
   (putnam-1978-b3-order-laws-p
    carrier zero add mul lt)
   (putnam-1978-b3-square-root-laws-p
    carrier zero mul lt square-root)
   (putnam-1978-b3-odd-root-laws-p
    carrier zero add mul odd-root)))

(defun putnam-1978-b3-p-value (p n)
  (apply$ p (list n)))

(defun putnam-1978-b3-a-value (a n)
  (apply$ a (list n)))

(defun putnam-1978-b3-root-upper-bound-p
    (p a n x carrier zero add mul lt)
  (implies
   (and
    (apply$ carrier (list x))
    (equal
     (putnam-1978-b3-polynomial-eval
      (putnam-1978-b3-p-value p n)
      x zero add mul)
     zero))
   (putnam-1978-b3-le
    lt x (putnam-1978-b3-a-value a n))))

(defun-sk putnam-1978-b3-source-hypotheses-p
    (p a carrier zero one add mul lt)
  (forall
   (n x)
   (implies
    (posp n)
    (let* ((two-n (* 2 n))
           (n-plus-one
            (putnam-1978-b3-field-natural
             (+ n 1) zero one add))
           (pn (putnam-1978-b3-p-value p n))
           (an (putnam-1978-b3-a-value a n)))
      (and
       (putnam-1978-b3-polynomial-p
        pn carrier zero)
       (apply$ carrier (list an))
       (equal
        (putnam-1978-b3-polynomial-eval
         pn an zero add mul)
        zero)
       (putnam-1978-b3-root-upper-bound-p
        p a n x carrier zero add mul lt)
       (equal
        (putnam-1978-b3-p-value p (+ two-n 1))
        (putnam-1978-b3-polynomial-add
         (putnam-1978-b3-p-value p two-n)
         (putnam-1978-b3-polynomial-x-scale
          n-plus-one
          (putnam-1978-b3-p-value p (- two-n 1))
          zero mul)
         zero add))
       (equal
        (putnam-1978-b3-p-value p (+ two-n 2))
        (putnam-1978-b3-polynomial-add
         (putnam-1978-b3-p-value p (+ two-n 1))
         (putnam-1978-b3-polynomial-x-scale
          n-plus-one
          (putnam-1978-b3-p-value p two-n)
          zero mul)
         zero add)))))))

(defun putnam-1978-b3-sequences-p
    (p a carrier zero one add mul lt)
  (and
   (tamep-functionp p)
   (tamep-functionp a)
   (equal
    (putnam-1978-b3-p-value p 1)
    (list one one))
   (equal
    (putnam-1978-b3-p-value p 2)
    (list
     one
     (putnam-1978-b3-field-natural
      2 zero one add)))
   (putnam-1978-b3-source-hypotheses-p
    p a carrier zero one add mul lt)))

(defun-sk putnam-1978-b3-strictly-increasing-p
    (a lt)
  (forall
   (i j)
   (implies
    (and
     (posp i)
     (posp j)
     (< i j))
    (putnam-1978-b3-lt
     lt
     (putnam-1978-b3-a-value a i)
     (putnam-1978-b3-a-value a j)))))

(defun putnam-1978-b3-abs (value zero neg lt)
  (if (putnam-1978-b3-lt lt value zero)
      (putnam-1978-b3-neg neg value)
    value))

(defun-sk putnam-1978-b3-convergence-tail-p
    (a epsilon start zero neg lt)
  (forall
   n
   (implies
    (and
     (posp n)
     (natp start)
     (<= start n))
    (putnam-1978-b3-lt
     lt
     (putnam-1978-b3-abs
      (putnam-1978-b3-a-value a n)
      zero neg lt)
     epsilon))))

(defun-sk putnam-1978-b3-convergence-start-exists-p
    (a epsilon zero neg lt)
  (exists
   start
   (and
    (natp start)
    (putnam-1978-b3-convergence-tail-p
     a epsilon start zero neg lt))))

(defun-sk putnam-1978-b3-converges-to-zero-p
    (a zero one add mul neg inv lt)
  (forall
   epsilon
   (implies
    (and
     (rationalp epsilon)
     (< 0 epsilon))
    (putnam-1978-b3-convergence-start-exists-p
     a
     (putnam-1978-b3-field-rational
      epsilon zero one add mul neg inv)
     zero neg lt))))

(defun putnambench-putnam-1978-b3-statement
    (carrier zero one add mul neg inv lt square-root odd-root p a)
  (implies
   (and
    (putnam-1978-b3-real-closed-field-p
     carrier zero one add mul neg inv lt square-root odd-root)
    (putnam-1978-b3-sequences-p
     p a carrier zero one add mul lt))
   (and
    (putnam-1978-b3-strictly-increasing-p a lt)
    (putnam-1978-b3-converges-to-zero-p
     a zero one add mul neg inv lt))))

(value-triple :itpeval-statement-checked)
:q
