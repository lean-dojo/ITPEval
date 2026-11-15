;; Statement-only formalization of PutnamBench corpus artifact putnam_1964_a2:
;; no positive continuous real-valued function on [0,1] has total integral 1
;; and first two moments alpha and alpha squared. This file contains no proof.

(in-package "ACL2")

(set-inhibit-output-lst '(prove proof-tree event summary))

;; The scalar arguments present the Dedekind-complete ordered field of real
;; numbers. Function objects are quantified internally. Continuity is the
;; epsilon-delta definition on [0,1], and the three interval integrals are
;; characterized by convergence of uniform left-endpoint Riemann sums. For
;; continuous real functions this is equivalent to the source's interval
;; Lebesgue integral. The benchmark's advertised solution is the empty set, so
;; its set equality is equivalently the absence of a qualifying function.

(defun p1964-member-p (carrier x)
  (if (apply$ carrier (list x)) t nil))

(defun p1964-binary (operation x y)
  (apply$ operation (list x y)))

(defun p1964-subtract (add negate x y)
  (p1964-binary add x (apply$ negate (list y))))

(defun p1964-less-equal-p (less x y)
  (not (apply$ less (list y x))))

(defun p1964-absolute (less negate zero x)
  (if (apply$ less (list x zero))
      (apply$ negate (list x))
    x))

(defun-sk p1964-field-laws-p
    (carrier zero one add multiply negate inverse)
  (forall (x y z)
    (implies
     (and (p1964-member-p carrier x)
          (p1964-member-p carrier y)
          (p1964-member-p carrier z))
     (and
      (p1964-member-p carrier (p1964-binary add x y))
      (p1964-member-p carrier (p1964-binary multiply x y))
      (p1964-member-p carrier (apply$ negate (list x)))
      (implies
       (not (equal x zero))
       (p1964-member-p carrier (apply$ inverse (list x))))
      (equal
       (p1964-binary add (p1964-binary add x y) z)
       (p1964-binary add x (p1964-binary add y z)))
      (equal (p1964-binary add x y)
             (p1964-binary add y x))
      (equal (p1964-binary add x zero) x)
      (equal (p1964-binary add x (apply$ negate (list x)))
             zero)
      (equal
       (p1964-binary multiply
                     (p1964-binary multiply x y) z)
       (p1964-binary multiply
                     x (p1964-binary multiply y z)))
      (equal (p1964-binary multiply x y)
             (p1964-binary multiply y x))
      (equal (p1964-binary multiply x one) x)
      (implies
       (not (equal x zero))
       (equal
        (p1964-binary multiply
                      x (apply$ inverse (list x)))
        one))
      (equal
       (p1964-binary multiply
                     x (p1964-binary add y z))
       (p1964-binary add
                     (p1964-binary multiply x y)
                     (p1964-binary multiply x z)))))))

(defun-sk p1964-order-laws-p
    (carrier zero add multiply less)
  (forall (x y z)
    (implies
     (and (p1964-member-p carrier x)
          (p1964-member-p carrier y)
          (p1964-member-p carrier z))
     (and
      (not (apply$ less (list x x)))
      (or (equal x y)
          (apply$ less (list x y))
          (apply$ less (list y x)))
      (implies
       (and (apply$ less (list x y))
            (apply$ less (list y z)))
       (apply$ less (list x z)))
      (implies
       (apply$ less (list x y))
       (apply$ less
               (list (p1964-binary add x z)
                     (p1964-binary add y z))))
      (implies
       (and (apply$ less (list zero x))
            (apply$ less (list zero y)))
       (apply$ less
               (list zero
                     (p1964-binary multiply x y))))))))

(defun-sk p1964-set-nonempty-p (carrier set)
  (exists (x)
    (and (p1964-member-p carrier x)
         (apply$ set (list x)))))

(defun-sk p1964-upper-bound-p (carrier less set bound)
  (forall (x)
    (implies
     (and (p1964-member-p carrier x)
          (apply$ set (list x)))
     (p1964-less-equal-p less x bound))))

(defun-sk p1964-bounded-above-p (carrier less set)
  (exists (bound)
    (and (p1964-member-p carrier bound)
         (p1964-upper-bound-p carrier less set bound))))

(defun-sk p1964-supremum-p (carrier less set supremum)
  (forall (bound)
    (and
     (p1964-member-p carrier supremum)
     (p1964-upper-bound-p carrier less set supremum)
     (implies
      (and (p1964-member-p carrier bound)
           (p1964-upper-bound-p carrier less set bound))
      (p1964-less-equal-p less supremum bound)))))

(defun-sk p1964-has-supremum-p (carrier less set)
  (exists (supremum)
    (p1964-supremum-p carrier less set supremum)))

(defun-sk p1964-dedekind-complete-p (carrier less)
  (forall (set)
    (implies
     (and (tamep-functionp set)
          (p1964-set-nonempty-p carrier set)
          (p1964-bounded-above-p carrier less set))
     (p1964-has-supremum-p carrier less set))))

(defun p1964-real-field-p
    (carrier zero one add multiply negate inverse less)
  (and
   (tamep-functionp carrier)
   (tamep-functionp add)
   (tamep-functionp multiply)
   (tamep-functionp negate)
   (tamep-functionp inverse)
   (tamep-functionp less)
   (p1964-member-p carrier zero)
   (p1964-member-p carrier one)
   (not (equal zero one))
   (p1964-field-laws-p
    carrier zero one add multiply negate inverse)
   (p1964-order-laws-p carrier zero add multiply less)
   (apply$ less (list zero one))
   (p1964-dedekind-complete-p carrier less)))

(defun-sk p1964-function-p (carrier function)
  (forall (x)
    (implies
     (p1964-member-p carrier x)
     (p1964-member-p carrier
                     (apply$ function (list x))))))

(defun p1964-unit-interval-p (carrier zero one less x)
  (and (p1964-member-p carrier x)
       (p1964-less-equal-p less zero x)
       (p1964-less-equal-p less x one)))

(defun-sk p1964-positive-on-unit-p
    (carrier zero one less function)
  (forall (x)
    (implies
     (p1964-unit-interval-p carrier zero one less x)
     (apply$ less
             (list zero (apply$ function (list x)))))))

(defun-sk p1964-continuity-neighborhood-p
    (carrier zero one add negate less function x epsilon delta)
  (forall (y)
    (implies
     (and
      (p1964-unit-interval-p carrier zero one less y)
      (apply$ less
              (list
               (p1964-absolute
                less negate zero
                (p1964-subtract add negate y x))
               delta)))
     (apply$ less
             (list
              (p1964-absolute
               less negate zero
               (p1964-subtract
                add negate
                (apply$ function (list y))
                (apply$ function (list x))))
              epsilon)))))

(defun-sk p1964-continuity-delta-exists-p
    (carrier zero one add negate less function x epsilon)
  (exists (delta)
    (and
     (p1964-member-p carrier delta)
     (apply$ less (list zero delta))
     (p1964-continuity-neighborhood-p
      carrier zero one add negate less
      function x epsilon delta))))

(defun-sk p1964-continuous-at-p
    (carrier zero one add negate less function x)
  (forall (epsilon)
    (implies
     (and (p1964-member-p carrier epsilon)
          (apply$ less (list zero epsilon)))
     (p1964-continuity-delta-exists-p
      carrier zero one add negate less
      function x epsilon))))

(defun-sk p1964-continuous-on-unit-p
    (carrier zero one add negate less function)
  (forall (x)
    (implies
     (p1964-unit-interval-p carrier zero one less x)
     (p1964-continuous-at-p
      carrier zero one add negate less function x))))

(defun p1964-natural-value (n zero one add)
  (declare (xargs :measure (nfix n)))
  (if (zp n)
      zero
    (p1964-binary
     add one
     (p1964-natural-value (- n 1) zero one add))))

(defun p1964-moment-weight (power x one multiply)
  (cond ((equal power 0) one)
        ((equal power 1) x)
        (t (p1964-binary multiply x x))))

(defun p1964-riemann-sum-aux
    (count n power function zero one add multiply inverse)
  (declare (xargs :measure (nfix count)))
  (if (zp count)
      zero
    (let* ((index (- count 1))
           (n-value
            (p1964-natural-value n zero one add))
           (index-value
            (p1964-natural-value index zero one add))
           (x
            (p1964-binary
             multiply index-value
             (apply$ inverse (list n-value))))
           (term
            (p1964-binary
             multiply
             (p1964-moment-weight power x one multiply)
             (apply$ function (list x)))))
      (p1964-binary
       add term
       (p1964-riemann-sum-aux
        (- count 1) n power function
        zero one add multiply inverse)))))

(defun p1964-riemann-sum
    (n power function zero one add multiply inverse)
  (let ((n-value
         (p1964-natural-value n zero one add)))
    (p1964-binary
     multiply
     (apply$ inverse (list n-value))
     (p1964-riemann-sum-aux
      n n power function zero one add multiply inverse))))

(defun-sk p1964-integral-tail-p
    (carrier zero one add multiply negate inverse less
     function power value epsilon cutoff)
  (forall (n)
    (implies
     (and (natp n)
          (<= 1 n)
          (<= cutoff n))
     (apply$ less
             (list
              (p1964-absolute
               less negate zero
               (p1964-subtract
                add negate
                (p1964-riemann-sum
                 n power function
                 zero one add multiply inverse)
                value))
              epsilon)))))

(defun-sk p1964-integral-cutoff-exists-p
    (carrier zero one add multiply negate inverse less
     function power value epsilon)
  (exists (cutoff)
    (and
     (natp cutoff)
     (p1964-integral-tail-p
      carrier zero one add multiply negate inverse less
      function power value epsilon cutoff))))

(defun-sk p1964-integral-value-p
    (carrier zero one add multiply negate inverse less
     function power value)
  (forall (epsilon)
    (implies
     (and (p1964-member-p carrier epsilon)
          (apply$ less (list zero epsilon)))
     (p1964-integral-cutoff-exists-p
      carrier zero one add multiply negate inverse less
      function power value epsilon))))

(defun p1964-qualifying-function-p
    (carrier zero one add multiply negate inverse less
     function alpha)
  (and
   (tamep-functionp function)
   (p1964-function-p carrier function)
   (p1964-positive-on-unit-p
    carrier zero one less function)
   (p1964-continuous-on-unit-p
    carrier zero one add negate less function)
   (p1964-integral-value-p
    carrier zero one add multiply negate inverse less
    function 0 one)
   (p1964-integral-value-p
    carrier zero one add multiply negate inverse less
    function 1 alpha)
   (p1964-integral-value-p
    carrier zero one add multiply negate inverse less
    function 2 (p1964-binary multiply alpha alpha))))

(defun-sk p1964-no-qualifying-function-p
    (carrier zero one add multiply negate inverse less alpha)
  (forall (function)
    (not
     (p1964-qualifying-function-p
      carrier zero one add multiply negate inverse less
      function alpha))))

(defun putnambench-putnam-1964-a2-statement
    (real-carrier real-zero real-one real-add real-multiply
     real-negate real-inverse real-less alpha)
  (implies
   (and
    (p1964-real-field-p
     real-carrier real-zero real-one real-add real-multiply
     real-negate real-inverse real-less)
    (p1964-member-p real-carrier alpha))
   (p1964-no-qualifying-function-p
    real-carrier real-zero real-one real-add real-multiply
    real-negate real-inverse real-less alpha)))

(value-triple :itpeval-statement-checked)
:q
