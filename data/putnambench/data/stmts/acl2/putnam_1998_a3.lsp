;; Statement-only formalization of PutnamBench corpus artifact putnam_1998_a3:
;; every real-valued function on the real line with continuous third
;; derivative has a point where f, f', f'', and f''' have nonnegative product.
;; This file contains no proof.

(in-package "ACL2")

(set-inhibit-output-lst '(prove proof-tree event summary))

;; The scalar arguments present a Dedekind-complete ordered field, hence a
;; presentation of the real numbers. Tame APPLY$ objects present arbitrary
;; real-valued functions. The three derivative functions and the concluding
;; point remain internally existentially quantified; differentiation and
;; continuity are expanded by their epsilon-delta definitions.

(defun p1998a3-member-p (carrier x)
  (if (apply$ carrier (list x)) t nil))

(defun p1998a3-unary (operation x)
  (apply$ operation (list x)))

(defun p1998a3-binary (operation x y)
  (apply$ operation (list x y)))

(defun p1998a3-subtract (add negate x y)
  (p1998a3-binary add x (p1998a3-unary negate y)))

(defun p1998a3-less-equal-p (less x y)
  (not (apply$ less (list y x))))

(defun p1998a3-absolute (less negate zero x)
  (if (apply$ less (list x zero))
      (p1998a3-unary negate x)
    x))

(defun-sk p1998a3-field-laws-p
    (carrier zero one add multiply negate inverse)
  (forall (x y z)
    (implies
     (and
      (p1998a3-member-p carrier x)
      (p1998a3-member-p carrier y)
      (p1998a3-member-p carrier z))
     (and
      (p1998a3-member-p
       carrier (p1998a3-binary add x y))
      (p1998a3-member-p
       carrier (p1998a3-binary multiply x y))
      (p1998a3-member-p
       carrier (p1998a3-unary negate x))
      (implies
       (not (equal x zero))
       (p1998a3-member-p
        carrier (p1998a3-unary inverse x)))
      (equal
       (p1998a3-binary add
                       (p1998a3-binary add x y)
                       z)
       (p1998a3-binary add
                       x
                       (p1998a3-binary add y z)))
      (equal
       (p1998a3-binary add x y)
       (p1998a3-binary add y x))
      (equal (p1998a3-binary add x zero) x)
      (equal
       (p1998a3-binary add x (p1998a3-unary negate x))
       zero)
      (equal
       (p1998a3-binary multiply
                       (p1998a3-binary multiply x y)
                       z)
       (p1998a3-binary multiply
                       x
                       (p1998a3-binary multiply y z)))
      (equal
       (p1998a3-binary multiply x y)
       (p1998a3-binary multiply y x))
      (equal (p1998a3-binary multiply x one) x)
      (implies
       (not (equal x zero))
       (equal
        (p1998a3-binary
         multiply x (p1998a3-unary inverse x))
        one))
      (equal
       (p1998a3-binary
        multiply x (p1998a3-binary add y z))
       (p1998a3-binary
        add
        (p1998a3-binary multiply x y)
        (p1998a3-binary multiply x z)))))))

(defun-sk p1998a3-order-laws-p
    (carrier zero add multiply less)
  (forall (x y z)
    (implies
     (and
      (p1998a3-member-p carrier x)
      (p1998a3-member-p carrier y)
      (p1998a3-member-p carrier z))
     (and
      (not (apply$ less (list x x)))
      (or
       (equal x y)
       (apply$ less (list x y))
       (apply$ less (list y x)))
      (implies
       (and
        (apply$ less (list x y))
        (apply$ less (list y z)))
       (apply$ less (list x z)))
      (implies
       (apply$ less (list x y))
       (apply$
        less
        (list
         (p1998a3-binary add x z)
         (p1998a3-binary add y z))))
      (implies
       (and
        (apply$ less (list zero x))
        (apply$ less (list zero y)))
       (apply$
        less
        (list
         zero
         (p1998a3-binary multiply x y))))))))

(defun-sk p1998a3-set-nonempty-p (carrier set)
  (exists (x)
    (and
     (p1998a3-member-p carrier x)
     (apply$ set (list x)))))

(defun-sk p1998a3-upper-bound-p
    (carrier less set bound)
  (forall (x)
    (implies
     (and
      (p1998a3-member-p carrier x)
      (apply$ set (list x)))
     (p1998a3-less-equal-p less x bound))))

(defun-sk p1998a3-bounded-above-p
    (carrier less set)
  (exists (bound)
    (and
     (p1998a3-member-p carrier bound)
     (p1998a3-upper-bound-p
      carrier less set bound))))

(defun-sk p1998a3-supremum-p
    (carrier less set supremum)
  (forall (bound)
    (and
     (p1998a3-member-p carrier supremum)
     (p1998a3-upper-bound-p
      carrier less set supremum)
     (implies
      (and
       (p1998a3-member-p carrier bound)
       (p1998a3-upper-bound-p
        carrier less set bound))
      (p1998a3-less-equal-p
       less supremum bound)))))

(defun-sk p1998a3-has-supremum-p
    (carrier less set)
  (exists (supremum)
    (p1998a3-supremum-p
     carrier less set supremum)))

(defun-sk p1998a3-dedekind-complete-p
    (carrier less)
  (forall (set)
    (implies
     (and
      (tamep-functionp set)
      (p1998a3-set-nonempty-p carrier set)
      (p1998a3-bounded-above-p carrier less set))
     (p1998a3-has-supremum-p
      carrier less set))))

(defun p1998a3-real-field-p
    (carrier zero one add multiply negate inverse less)
  (and
   (tamep-functionp carrier)
   (tamep-functionp add)
   (tamep-functionp multiply)
   (tamep-functionp negate)
   (tamep-functionp inverse)
   (tamep-functionp less)
   (p1998a3-member-p carrier zero)
   (p1998a3-member-p carrier one)
   (not (equal zero one))
   (p1998a3-field-laws-p
    carrier zero one add multiply negate inverse)
   (p1998a3-order-laws-p
    carrier zero add multiply less)
   (apply$ less (list zero one))
   (p1998a3-dedekind-complete-p carrier less)))

(defun-sk p1998a3-real-function-p
    (carrier function)
  (forall (x)
    (implies
     (p1998a3-member-p carrier x)
     (p1998a3-member-p
      carrier (apply$ function (list x))))))

(defun p1998a3-positive-p
    (carrier zero less x)
  (and
   (p1998a3-member-p carrier x)
   (apply$ less (list zero x))))

;; Global epsilon-delta continuity on the real carrier.

(defun-sk p1998a3-continuity-neighborhood-p
    (carrier zero add negate less function x epsilon delta)
  (forall (y)
    (implies
     (and
      (p1998a3-member-p carrier y)
      (apply$
       less
       (list
        (p1998a3-absolute
         less negate zero
         (p1998a3-subtract add negate y x))
        delta)))
     (apply$
      less
      (list
       (p1998a3-absolute
        less negate zero
        (p1998a3-subtract
         add negate
         (apply$ function (list y))
         (apply$ function (list x))))
       epsilon)))))

(defun-sk p1998a3-continuity-radius-exists-p
    (carrier zero add negate less function x epsilon)
  (exists (delta)
    (and
     (p1998a3-positive-p carrier zero less delta)
     (p1998a3-continuity-neighborhood-p
      carrier zero add negate less
      function x epsilon delta))))

(defun-sk p1998a3-continuous-at-p
    (carrier zero add negate less function x)
  (forall (epsilon)
    (implies
     (p1998a3-positive-p
      carrier zero less epsilon)
     (p1998a3-continuity-radius-exists-p
      carrier zero add negate less
      function x epsilon))))

(defun-sk p1998a3-continuous-p
    (carrier zero add negate less function)
  (forall (x)
    (implies
     (p1998a3-member-p carrier x)
     (p1998a3-continuous-at-p
      carrier zero add negate less function x))))

;; The derivative relation is expressed without division:
;; |g(y) - g(x) - d * (y - x)| <= epsilon * |y - x|
;; throughout a sufficiently small neighborhood of x.

(defun-sk p1998a3-derivative-neighborhood-p
    (carrier zero add multiply negate less
     function x derivative epsilon delta)
  (forall (y)
    (implies
     (and
      (p1998a3-member-p carrier y)
      (apply$
       less
       (list
        (p1998a3-absolute
         less negate zero
         (p1998a3-subtract add negate y x))
        delta)))
     (p1998a3-less-equal-p
      less
      (p1998a3-absolute
       less negate zero
       (p1998a3-subtract
        add negate
        (p1998a3-subtract
         add negate
         (apply$ function (list y))
         (apply$ function (list x)))
        (p1998a3-binary
         multiply derivative
         (p1998a3-subtract add negate y x))))
      (p1998a3-binary
       multiply epsilon
       (p1998a3-absolute
        less negate zero
        (p1998a3-subtract add negate y x)))))))

(defun-sk p1998a3-derivative-radius-exists-p
    (carrier zero add multiply negate less
     function x derivative epsilon)
  (exists (delta)
    (and
     (p1998a3-positive-p carrier zero less delta)
     (p1998a3-derivative-neighborhood-p
      carrier zero add multiply negate less
      function x derivative epsilon delta))))

(defun-sk p1998a3-derivative-epsilon-condition-p
    (carrier zero add multiply negate less
     function x derivative)
  (forall (epsilon)
    (implies
     (p1998a3-positive-p carrier zero less epsilon)
     (p1998a3-derivative-radius-exists-p
      carrier zero add multiply negate less
      function x derivative epsilon))))

(defun p1998a3-has-derivative-at-p
    (carrier zero add multiply negate less
     function x derivative)
  (and
   (p1998a3-member-p carrier x)
   (p1998a3-member-p carrier derivative)
   (p1998a3-derivative-epsilon-condition-p
    carrier zero add multiply negate less
    function x derivative)))

(defun-sk p1998a3-derivative-function-p
    (carrier zero add multiply negate less
     function derivative-function)
  (forall (x)
    (implies
     (p1998a3-member-p carrier x)
     (p1998a3-has-derivative-at-p
      carrier zero add multiply negate less
      function x
      (apply$ derivative-function (list x))))))

(defun p1998a3-c3-chain-p
    (carrier zero add multiply negate less
     function f1 f2 f3)
  (and
   (tamep-functionp function)
   (tamep-functionp f1)
   (tamep-functionp f2)
   (tamep-functionp f3)
   (p1998a3-real-function-p carrier function)
   (p1998a3-real-function-p carrier f1)
   (p1998a3-real-function-p carrier f2)
   (p1998a3-real-function-p carrier f3)
   (p1998a3-derivative-function-p
    carrier zero add multiply negate less
    function f1)
   (p1998a3-derivative-function-p
    carrier zero add multiply negate less
    f1 f2)
   (p1998a3-derivative-function-p
    carrier zero add multiply negate less
    f2 f3)
   (p1998a3-continuous-p
    carrier zero add negate less f3)))

(defun-sk p1998a3-c3-witnesses-p
    (carrier zero add multiply negate less function)
  (exists (f1 f2 f3)
    (p1998a3-c3-chain-p
     carrier zero add multiply negate less
     function f1 f2 f3)))

(defun p1998a3-fourfold-product
    (multiply function f1 f2 f3 x)
  (p1998a3-binary
   multiply
   (p1998a3-binary
    multiply
    (p1998a3-binary
     multiply
     (apply$ function (list x))
     (apply$ f1 (list x)))
    (apply$ f2 (list x)))
   (apply$ f3 (list x))))

(defun-sk p1998a3-good-point-witnesses-p
    (carrier zero add multiply negate less function)
  (exists (f1 f2 f3 x)
    (and
     (p1998a3-c3-chain-p
      carrier zero add multiply negate less
      function f1 f2 f3)
     (p1998a3-member-p carrier x)
     (p1998a3-less-equal-p
      less zero
      (p1998a3-fourfold-product
       multiply function f1 f2 f3 x)))))

(defun putnambench-putnam-1998-a3-statement
    (real-carrier real-zero real-one real-add real-multiply
     real-negate real-inverse real-less function)
  (implies
   (and
   (p1998a3-real-field-p
     real-carrier real-zero real-one real-add real-multiply
     real-negate real-inverse real-less)
    (tamep-functionp function)
    (p1998a3-real-function-p real-carrier function)
    (p1998a3-c3-witnesses-p
     real-carrier real-zero real-add real-multiply
     real-negate real-less function))
   (p1998a3-good-point-witnesses-p
    real-carrier real-zero real-add real-multiply
    real-negate real-less function)))

(value-triple :itpeval-statement-checked)
:q
