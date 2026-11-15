;; Statement-only formalization of PutnamBench corpus artifact putnam_1964_b3:
;; a continuous real-valued function that tends to zero along every positive
;; arithmetic ray n*alpha tends to zero as its real argument tends to infinity.
;; This file contains no proof.

(in-package "ACL2")

(set-inhibit-output-lst '(prove proof-tree event summary))

;; The scalar arguments present the Dedekind-complete ordered field of real
;; numbers. A tame APPLY$ object presents the arbitrary function. Continuity
;; and both limits use their epsilon characterizations, with every radius,
;; cutoff, and tail bound quantified internally.

(defun p1964b3-member-p (carrier x)
  (if (apply$ carrier (list x)) t nil))

(defun p1964b3-unary (operation x)
  (apply$ operation (list x)))

(defun p1964b3-binary (operation x y)
  (apply$ operation (list x y)))

(defun p1964b3-subtract (add negate x y)
  (p1964b3-binary add x (p1964b3-unary negate y)))

(defun p1964b3-less-equal-p (less x y)
  (not (apply$ less (list y x))))

(defun p1964b3-absolute (less negate zero x)
  (if (apply$ less (list x zero))
      (p1964b3-unary negate x)
    x))

(defun-sk p1964b3-field-laws-p
    (carrier zero one add multiply negate inverse)
  (forall (x y z)
    (implies
     (and
      (p1964b3-member-p carrier x)
      (p1964b3-member-p carrier y)
      (p1964b3-member-p carrier z))
     (and
      (p1964b3-member-p
       carrier (p1964b3-binary add x y))
      (p1964b3-member-p
       carrier (p1964b3-binary multiply x y))
      (p1964b3-member-p
       carrier (p1964b3-unary negate x))
      (implies
       (not (equal x zero))
       (p1964b3-member-p
        carrier (p1964b3-unary inverse x)))
      (equal
       (p1964b3-binary add
                       (p1964b3-binary add x y)
                       z)
       (p1964b3-binary add
                       x
                       (p1964b3-binary add y z)))
      (equal
       (p1964b3-binary add x y)
       (p1964b3-binary add y x))
      (equal (p1964b3-binary add x zero) x)
      (equal
       (p1964b3-binary add x (p1964b3-unary negate x))
       zero)
      (equal
       (p1964b3-binary multiply
                       (p1964b3-binary multiply x y)
                       z)
       (p1964b3-binary multiply
                       x
                       (p1964b3-binary multiply y z)))
      (equal
       (p1964b3-binary multiply x y)
       (p1964b3-binary multiply y x))
      (equal (p1964b3-binary multiply x one) x)
      (implies
       (not (equal x zero))
       (equal
        (p1964b3-binary
         multiply x (p1964b3-unary inverse x))
        one))
      (equal
       (p1964b3-binary
        multiply x (p1964b3-binary add y z))
       (p1964b3-binary
        add
        (p1964b3-binary multiply x y)
        (p1964b3-binary multiply x z)))))))

(defun-sk p1964b3-order-laws-p
    (carrier zero add multiply less)
  (forall (x y z)
    (implies
     (and
      (p1964b3-member-p carrier x)
      (p1964b3-member-p carrier y)
      (p1964b3-member-p carrier z))
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
         (p1964b3-binary add x z)
         (p1964b3-binary add y z))))
      (implies
       (and
        (apply$ less (list zero x))
        (apply$ less (list zero y)))
       (apply$
        less
        (list
         zero
         (p1964b3-binary multiply x y))))))))

(defun-sk p1964b3-set-nonempty-p (carrier set)
  (exists (x)
    (and
     (p1964b3-member-p carrier x)
     (apply$ set (list x)))))

(defun-sk p1964b3-upper-bound-p
    (carrier less set bound)
  (forall (x)
    (implies
     (and
      (p1964b3-member-p carrier x)
      (apply$ set (list x)))
     (p1964b3-less-equal-p less x bound))))

(defun-sk p1964b3-bounded-above-p
    (carrier less set)
  (exists (bound)
    (and
     (p1964b3-member-p carrier bound)
     (p1964b3-upper-bound-p
      carrier less set bound))))

(defun-sk p1964b3-supremum-p
    (carrier less set supremum)
  (forall (bound)
    (and
     (p1964b3-member-p carrier supremum)
     (p1964b3-upper-bound-p
      carrier less set supremum)
     (implies
      (and
       (p1964b3-member-p carrier bound)
       (p1964b3-upper-bound-p
        carrier less set bound))
      (p1964b3-less-equal-p
       less supremum bound)))))

(defun-sk p1964b3-has-supremum-p
    (carrier less set)
  (exists (supremum)
    (p1964b3-supremum-p
     carrier less set supremum)))

(defun-sk p1964b3-dedekind-complete-p
    (carrier less)
  (forall (set)
    (implies
     (and
      (tamep-functionp set)
      (p1964b3-set-nonempty-p carrier set)
      (p1964b3-bounded-above-p carrier less set))
     (p1964b3-has-supremum-p
      carrier less set))))

(defun p1964b3-real-field-p
    (carrier zero one add multiply negate inverse less)
  (and
   (tamep-functionp carrier)
   (tamep-functionp add)
   (tamep-functionp multiply)
   (tamep-functionp negate)
   (tamep-functionp inverse)
   (tamep-functionp less)
   (p1964b3-member-p carrier zero)
   (p1964b3-member-p carrier one)
   (not (equal zero one))
   (p1964b3-field-laws-p
    carrier zero one add multiply negate inverse)
   (p1964b3-order-laws-p
    carrier zero add multiply less)
   (apply$ less (list zero one))
   (p1964b3-dedekind-complete-p carrier less)))

(defun-sk p1964b3-real-function-p
    (carrier function)
  (forall (x)
    (implies
     (p1964b3-member-p carrier x)
     (p1964b3-member-p
      carrier (apply$ function (list x))))))

(defun p1964b3-positive-p
    (carrier zero less x)
  (and
   (p1964b3-member-p carrier x)
   (apply$ less (list zero x))))

;; Global epsilon-delta continuity on the real carrier.

(defun-sk p1964b3-continuity-neighborhood-p
    (carrier zero add negate less function x epsilon delta)
  (forall (y)
    (implies
     (and
      (p1964b3-member-p carrier y)
      (apply$
       less
       (list
        (p1964b3-absolute
         less negate zero
         (p1964b3-subtract add negate y x))
        delta)))
     (apply$
      less
      (list
       (p1964b3-absolute
        less negate zero
        (p1964b3-subtract
         add negate
         (apply$ function (list y))
         (apply$ function (list x))))
       epsilon)))))

(defun-sk p1964b3-continuity-radius-exists-p
    (carrier zero add negate less function x epsilon)
  (exists (delta)
    (and
     (p1964b3-positive-p carrier zero less delta)
     (p1964b3-continuity-neighborhood-p
      carrier zero add negate less
      function x epsilon delta))))

(defun-sk p1964b3-continuous-at-p
    (carrier zero add negate less function x)
  (forall (epsilon)
    (implies
     (p1964b3-positive-p
      carrier zero less epsilon)
     (p1964b3-continuity-radius-exists-p
      carrier zero add negate less
      function x epsilon))))

(defun-sk p1964b3-continuous-p
    (carrier zero add negate less function)
  (forall (x)
    (implies
     (p1964b3-member-p carrier x)
     (p1964b3-continuous-at-p
      carrier zero add negate less function x))))

;; Repeated addition is the ordered-field value of the natural multiple
;; n*alpha appearing in each arithmetic ray.

(defun p1964b3-natural-multiple
    (n alpha zero add)
  (declare (xargs :measure (nfix n)))
  (if (zp n)
      zero
    (p1964b3-binary
     add
     alpha
     (p1964b3-natural-multiple
      (- n 1) alpha zero add))))

(defun-sk p1964b3-ray-tail-p
    (zero add negate less function alpha epsilon cutoff)
  (forall (n)
    (implies
     (and
      (natp n)
      (<= cutoff n))
     (apply$
      less
      (list
       (p1964b3-absolute
        less negate zero
        (p1964b3-subtract
         add negate
         (apply$
          function
          (list
           (p1964b3-natural-multiple
            n alpha zero add)))
         zero))
       epsilon)))))

(defun-sk p1964b3-ray-cutoff-exists-p
    (zero add negate less function alpha epsilon)
  (exists (cutoff)
    (and
     (natp cutoff)
     (p1964b3-ray-tail-p
      zero add negate less
      function alpha epsilon cutoff))))

(defun-sk p1964b3-ray-converges-to-zero-p
    (carrier zero add negate less function alpha)
  (forall (epsilon)
    (implies
     (p1964b3-positive-p
      carrier zero less epsilon)
     (p1964b3-ray-cutoff-exists-p
      zero add negate less
      function alpha epsilon))))

(defun-sk p1964b3-all-positive-rays-converge-p
    (carrier zero add negate less function)
  (forall (alpha)
    (implies
     (p1964b3-positive-p
      carrier zero less alpha)
     (p1964b3-ray-converges-to-zero-p
      carrier zero add negate less
      function alpha))))

;; Epsilon-tail convergence of f(x) to zero as x tends to +infinity in R.

(defun-sk p1964b3-real-tail-p
    (carrier zero add negate less function epsilon bound)
  (forall (x)
    (implies
     (and
      (p1964b3-member-p carrier x)
      (p1964b3-less-equal-p less bound x))
     (apply$
      less
      (list
       (p1964b3-absolute
        less negate zero
        (p1964b3-subtract
         add negate
         (apply$ function (list x))
         zero))
       epsilon)))))

(defun-sk p1964b3-real-tail-bound-exists-p
    (carrier zero add negate less function epsilon)
  (exists (bound)
    (and
     (p1964b3-member-p carrier bound)
     (p1964b3-real-tail-p
      carrier zero add negate less
      function epsilon bound))))

(defun-sk p1964b3-tends-to-zero-at-infinity-p
    (carrier zero add negate less function)
  (forall (epsilon)
    (implies
     (p1964b3-positive-p
      carrier zero less epsilon)
     (p1964b3-real-tail-bound-exists-p
      carrier zero add negate less
      function epsilon))))

(defun putnambench-putnam-1964-b3-statement
    (real-carrier real-zero real-one real-add real-multiply
     real-negate real-inverse real-less function)
  (implies
   (and
    (p1964b3-real-field-p
     real-carrier real-zero real-one real-add real-multiply
     real-negate real-inverse real-less)
    (tamep-functionp function)
    (p1964b3-real-function-p real-carrier function)
    (p1964b3-continuous-p
     real-carrier real-zero real-add real-negate
     real-less function)
    (p1964b3-all-positive-rays-converge-p
     real-carrier real-zero real-add real-negate
     real-less function))
   (p1964b3-tends-to-zero-at-infinity-p
    real-carrier real-zero real-add real-negate
    real-less function)))

(value-triple :itpeval-statement-checked)
:q
