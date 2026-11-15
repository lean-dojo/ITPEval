;; Statement-only formalization of Babel-formal artifact circle_average:
;; circle maps and circle averages over an arbitrary commutative additive
;; monoid with an extensional, constant-preserving, additive, and
;; translation-invariant integral, asserting the source's seventeen
;; identities. This file contains no proof.

(in-package "ACL2")

(set-inhibit-output-lst '(prove proof-tree event summary))

;; These conservative symbols present an arbitrary carrier, an unbounded sort
;; of unary functions on that carrier, their application operation, and the
;; generic integral.  The constructor symbols represent exactly the lambda
;; terms used by the source statements.  Their typing and evaluation rules,
;; together with every monoid and integral law, remain explicit hypotheses.

(defstub ca-r-p (x) t)
(defstub ca-function-p (function) t)
(defstub ca-zero () t)
(defstub ca-add (left right) t)
(defstub ca-apply (function argument) t)
(defstub ca-integral (function) t)
(defstub ca-constant-function (constant) t)
(defstub ca-pointwise-add-function (left right) t)
(defstub ca-shift-function (function center) t)
(defstub ca-average-function (function) t)

(defun ca-circle-map (center theta)
  (ca-add theta center))

(defun ca-circle-average (function center)
  (ca-integral (ca-shift-function function center)))

(defun-sk ca-add-monoid-laws-p ()
  (forall (x y z)
    (implies
     (and (ca-r-p x)
          (ca-r-p y)
          (ca-r-p z))
     (and
      (ca-r-p (ca-add x y))
      (equal (ca-add x (ca-zero)) x)
      (equal (ca-add x y) (ca-add y x))
      (equal (ca-add (ca-add x y) z)
             (ca-add x (ca-add y z)))))))

(defun-sk ca-functions-extensionally-equal-p (left right)
  (forall (theta)
    (implies
     (ca-r-p theta)
     (equal (ca-apply left theta)
            (ca-apply right theta)))))

(defun-sk ca-function-space-laws-p ()
  (forall (f g c theta)
    (and
     (implies
      (and (ca-function-p f)
           (ca-r-p theta))
      (ca-r-p (ca-apply f theta)))
     (implies
      (ca-r-p c)
      (and
       (ca-function-p (ca-constant-function c))
       (implies
        (ca-r-p theta)
        (equal
         (ca-apply (ca-constant-function c) theta)
         c))))
     (implies
      (and (ca-function-p f)
           (ca-function-p g))
      (and
       (ca-function-p (ca-pointwise-add-function f g))
       (implies
        (ca-r-p theta)
        (equal
         (ca-apply
          (ca-pointwise-add-function f g)
          theta)
         (ca-add (ca-apply f theta)
                 (ca-apply g theta))))))
     (implies
      (and (ca-function-p f)
           (ca-r-p c))
      (and
       (ca-function-p (ca-shift-function f c))
       (implies
        (ca-r-p theta)
        (equal
         (ca-apply (ca-shift-function f c) theta)
         (ca-apply f (ca-add theta c))))))
     (implies
      (ca-function-p f)
      (and
       (ca-function-p (ca-average-function f))
       (implies
        (ca-r-p theta)
        (equal
         (ca-apply (ca-average-function f) theta)
         (ca-circle-average f theta))))))))

(defun-sk ca-integral-laws-p ()
  (forall (f g c)
    (and
     (implies
      (ca-function-p f)
      (ca-r-p (ca-integral f)))
     (implies
      (and (ca-function-p f)
           (ca-function-p g)
           (ca-functions-extensionally-equal-p f g))
      (equal (ca-integral f)
             (ca-integral g)))
     (implies
      (ca-r-p c)
      (equal
       (ca-integral (ca-constant-function c))
       c))
     (implies
      (and (ca-function-p f)
           (ca-function-p g))
      (equal
       (ca-integral (ca-pointwise-add-function f g))
       (ca-add (ca-integral f)
               (ca-integral g))))
     (implies
      (and (ca-function-p f)
           (ca-r-p c))
      (equal
       (ca-integral (ca-shift-function f c))
       (ca-integral f))))))

(defun ca-circle-average-context-p ()
  (and
   (ca-r-p (ca-zero))
   (ca-add-monoid-laws-p)
   (ca-function-space-laws-p)
   (ca-integral-laws-p)))

(defun-sk ca-circle-map-zero-statement ()
  (forall (theta)
    (implies
     (and (ca-circle-average-context-p)
          (ca-r-p theta))
     (equal
      (ca-circle-map (ca-zero) theta)
      theta))))

(defun-sk ca-circle-average-zero-statement ()
  (forall (f)
    (implies
     (and (ca-circle-average-context-p)
          (ca-function-p f))
     (equal
      (ca-circle-average f (ca-zero))
      (ca-integral f)))))

(defun-sk ca-circle-average-add-statement ()
  (forall (f g c)
    (implies
     (and (ca-circle-average-context-p)
          (ca-function-p f)
          (ca-function-p g)
          (ca-r-p c))
     (equal
      (ca-circle-average
       (ca-pointwise-add-function f g)
       c)
      (ca-add
       (ca-circle-average f c)
       (ca-circle-average g c))))))

(defun-sk ca-circle-average-fun-add-statement ()
  (forall (f c)
    (implies
     (and (ca-circle-average-context-p)
          (ca-function-p f)
          (ca-r-p c))
     (equal
      (ca-circle-average
       (ca-shift-function f c)
       (ca-zero))
      (ca-circle-average f c)))))

(defun-sk ca-circle-map-add-statement ()
  (forall (c d theta)
    (implies
     (and (ca-circle-average-context-p)
          (ca-r-p c)
          (ca-r-p d)
          (ca-r-p theta))
     (equal
      (ca-circle-map (ca-add c d) theta)
      (ca-circle-map c (ca-circle-map d theta))))))

(defun-sk ca-circle-average-shift-statement ()
  (forall (f c d)
    (implies
     (and (ca-circle-average-context-p)
          (ca-function-p f)
          (ca-r-p c)
          (ca-r-p d))
     (equal
      (ca-circle-average f (ca-add c d))
      (ca-circle-average
       (ca-shift-function f d)
       c)))))

(defun-sk ca-circle-average-const-statement ()
  (forall (k c)
    (implies
     (and (ca-circle-average-context-p)
          (ca-r-p k)
          (ca-r-p c))
     (equal
      (ca-circle-average
       (ca-constant-function k)
       c)
      k))))

(defun-sk ca-circle-average-add-const-statement ()
  (forall (f k c)
    (implies
     (and (ca-circle-average-context-p)
          (ca-function-p f)
          (ca-r-p k)
          (ca-r-p c))
     (equal
      (ca-circle-average
       (ca-pointwise-add-function
        f
        (ca-constant-function k))
       c)
      (ca-add
       (ca-circle-average f c)
       k)))))

(defun-sk ca-circle-average-comm-add-statement ()
  (forall (f g c)
    (implies
     (and (ca-circle-average-context-p)
          (ca-function-p f)
          (ca-function-p g)
          (ca-r-p c))
     (equal
      (ca-circle-average
       (ca-pointwise-add-function f g)
       c)
      (ca-circle-average
       (ca-pointwise-add-function g f)
       c)))))

(defun-sk ca-circle-average-add-assoc-statement ()
  (forall (f g h c)
    (implies
     (and (ca-circle-average-context-p)
          (ca-function-p f)
          (ca-function-p g)
          (ca-function-p h)
          (ca-r-p c))
     (equal
      (ca-circle-average
       (ca-pointwise-add-function
        (ca-pointwise-add-function f g)
        h)
       c)
      (ca-add
       (ca-circle-average f c)
       (ca-add
        (ca-circle-average g c)
        (ca-circle-average h c)))))))

(defun-sk ca-circle-average-center-comm-statement ()
  (forall (f c d)
    (implies
     (and (ca-circle-average-context-p)
          (ca-function-p f)
          (ca-r-p c)
          (ca-r-p d))
     (equal
      (ca-circle-average f (ca-add c d))
      (ca-circle-average f (ca-add d c))))))

(defun-sk ca-circle-average-center-independent-statement ()
  (forall (f c)
    (implies
     (and (ca-circle-average-context-p)
          (ca-function-p f)
          (ca-r-p c))
     (equal
      (ca-circle-average f c)
      (ca-integral f)))))

(defun-sk ca-circle-average-center-eq-statement ()
  (forall (f c d)
    (implies
     (and (ca-circle-average-context-p)
          (ca-function-p f)
          (ca-r-p c)
          (ca-r-p d))
     (equal
      (ca-circle-average f c)
      (ca-circle-average f d)))))

(defun-sk ca-circle-average-idempotent-statement ()
  (forall (f c)
    (implies
     (and (ca-circle-average-context-p)
          (ca-function-p f)
          (ca-r-p c))
     (equal
      (ca-circle-average
       (ca-average-function f)
       c)
      (ca-circle-average f c)))))

(defun-sk ca-circle-average-of-zero-integral-statement ()
  (forall (f c)
    (implies
     (and (ca-circle-average-context-p)
          (ca-function-p f)
          (ca-r-p c)
          (equal (ca-integral f)
                 (ca-zero)))
     (equal
      (ca-circle-average f c)
      (ca-zero)))))

(defun-sk ca-circle-average-linear-statement ()
  (forall (f g c)
    (implies
     (and (ca-circle-average-context-p)
          (ca-function-p f)
          (ca-function-p g)
          (ca-r-p c))
     (equal
      (ca-circle-average
       (ca-pointwise-add-function f g)
       c)
      (ca-add
       (ca-circle-average f c)
       (ca-circle-average g c))))))

(defun-sk ca-circle-average-shift-commute-statement ()
  (forall (f c d)
    (implies
     (and (ca-circle-average-context-p)
          (ca-function-p f)
          (ca-r-p c)
          (ca-r-p d))
     (equal
      (ca-circle-average
       (ca-shift-function f d)
       c)
      (ca-circle-average
       f
       (ca-add c d))))))

(defun circle-average-statement ()
  (and
   (ca-circle-map-zero-statement)
   (ca-circle-average-zero-statement)
   (ca-circle-average-add-statement)
   (ca-circle-average-fun-add-statement)
   (ca-circle-map-add-statement)
   (ca-circle-average-shift-statement)
   (ca-circle-average-const-statement)
   (ca-circle-average-add-const-statement)
   (ca-circle-average-comm-add-statement)
   (ca-circle-average-add-assoc-statement)
   (ca-circle-average-center-comm-statement)
   (ca-circle-average-center-independent-statement)
   (ca-circle-average-center-eq-statement)
   (ca-circle-average-idempotent-statement)
   (ca-circle-average-of-zero-integral-statement)
   (ca-circle-average-linear-statement)
   (ca-circle-average-shift-commute-statement)))

(value-triple :itpeval-statement-checked)
:q
