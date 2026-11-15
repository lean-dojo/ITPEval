;; Statement-only formalization of PutnamBench corpus artifact putnam_2023_b4:
;; among continuous real functions with prescribed derivative resets and
;; piecewise constant second derivative, the least elapsed time to rise from
;; 1/2 to 2023 is 29. This file contains no proof.

(in-package "ACL2")

(set-inhibit-output-lst '(prove proof-tree event summary))

;; The scalar parameters present a Dedekind-complete ordered field, hence a
;; copy of the real numbers. Function objects present the sequence of reset
;; times, the function, and its first and second derivatives. Continuity,
;; differentiability, one-sided limits, and the least-time conclusion are
;; stated directly by their quantified definitions; no closed-form motion
;; formula is assumed.

(defun p2023b4-member-p (carrier x)
  (if (apply$ carrier (list x)) t nil))

(defun p2023b4-call1 (function x)
  (apply$ function (list x)))

(defun p2023b4-call2 (operation x y)
  (apply$ operation (list x y)))

(defun p2023b4-add (add x y)
  (p2023b4-call2 add x y))

(defun p2023b4-mul (mul x y)
  (p2023b4-call2 mul x y))

(defun p2023b4-neg (neg x)
  (p2023b4-call1 neg x))

(defun p2023b4-sub (add neg x y)
  (p2023b4-add add x (p2023b4-neg neg y)))

(defun p2023b4-lt (lt x y)
  (if (p2023b4-call2 lt x y) t nil))

(defun p2023b4-le (lt x y)
  (not (p2023b4-lt lt y x)))

(defun p2023b4-positive-p (carrier zero lt x)
  (and
   (p2023b4-member-p carrier x)
   (p2023b4-lt lt zero x)))

(defun p2023b4-abs (zero neg lt x)
  (if (p2023b4-lt lt x zero)
      (p2023b4-neg neg x)
    x))

(defun p2023b4-nat-real (n zero one add)
  (declare (xargs :measure (nfix n)))
  (if (zp n)
      zero
    (p2023b4-add
     add one
     (p2023b4-nat-real (- n 1) zero one add))))

(defun p2023b4-one-half (one add mul inv)
  (p2023b4-mul
   mul one
   (p2023b4-call1 inv (p2023b4-add add one one))))

(defun-sk p2023b4-field-laws-p
    (carrier zero one add mul neg inv)
  (forall (x y z)
    (implies
     (and
      (p2023b4-member-p carrier x)
      (p2023b4-member-p carrier y)
      (p2023b4-member-p carrier z))
     (and
      (p2023b4-member-p carrier (p2023b4-add add x y))
      (p2023b4-member-p carrier (p2023b4-mul mul x y))
      (p2023b4-member-p carrier (p2023b4-neg neg x))
      (p2023b4-member-p carrier (p2023b4-call1 inv x))
      (equal
       (p2023b4-add add (p2023b4-add add x y) z)
       (p2023b4-add add x (p2023b4-add add y z)))
      (equal (p2023b4-add add x y)
             (p2023b4-add add y x))
      (equal (p2023b4-add add x zero) x)
      (equal (p2023b4-add add x (p2023b4-neg neg x))
             zero)
      (equal
       (p2023b4-mul mul (p2023b4-mul mul x y) z)
       (p2023b4-mul mul x (p2023b4-mul mul y z)))
      (equal (p2023b4-mul mul x y)
             (p2023b4-mul mul y x))
      (equal (p2023b4-mul mul x one) x)
      (implies
       (not (equal x zero))
       (equal
        (p2023b4-mul mul x (p2023b4-call1 inv x))
        one))
      (equal
       (p2023b4-mul mul x (p2023b4-add add y z))
       (p2023b4-add
        add
        (p2023b4-mul mul x y)
        (p2023b4-mul mul x z)))))))

(defun-sk p2023b4-order-laws-p
    (carrier zero add mul lt)
  (forall (x y z)
    (implies
     (and
      (p2023b4-member-p carrier x)
      (p2023b4-member-p carrier y)
      (p2023b4-member-p carrier z))
     (and
      (not (p2023b4-lt lt x x))
      (or (equal x y)
          (p2023b4-lt lt x y)
          (p2023b4-lt lt y x))
      (implies
       (and (p2023b4-lt lt x y)
            (p2023b4-lt lt y z))
       (p2023b4-lt lt x z))
      (implies
       (p2023b4-lt lt x y)
       (p2023b4-lt
        lt
        (p2023b4-add add x z)
        (p2023b4-add add y z)))
      (implies
       (and
        (p2023b4-lt lt zero x)
        (p2023b4-lt lt zero y))
       (p2023b4-lt lt zero (p2023b4-mul mul x y)))))))

(defun-sk p2023b4-set-nonempty-p (carrier set)
  (exists (x)
    (and
     (p2023b4-member-p carrier x)
     (p2023b4-call1 set x))))

(defun-sk p2023b4-upper-bound-p (carrier lt set bound)
  (forall (x)
    (implies
     (and
      (p2023b4-member-p carrier x)
      (p2023b4-call1 set x))
     (p2023b4-le lt x bound))))

(defun-sk p2023b4-bounded-above-p (carrier lt set)
  (exists (bound)
    (and
     (p2023b4-member-p carrier bound)
     (p2023b4-upper-bound-p carrier lt set bound))))

(defun-sk p2023b4-least-upper-bound-p
    (carrier lt set supremum)
  (forall (bound)
    (implies
     (and
      (p2023b4-member-p carrier bound)
      (p2023b4-upper-bound-p carrier lt set bound))
     (p2023b4-le lt supremum bound))))

(defun p2023b4-supremum-p (carrier lt set supremum)
  (and
   (p2023b4-member-p carrier supremum)
   (p2023b4-upper-bound-p carrier lt set supremum)
   (p2023b4-least-upper-bound-p
    carrier lt set supremum)))

(defun-sk p2023b4-has-supremum-p (carrier lt set)
  (exists (supremum)
    (p2023b4-supremum-p carrier lt set supremum)))

(defun-sk p2023b4-dedekind-complete-p (carrier lt)
  (forall (set)
    (implies
     (and
      (tamep-functionp set)
      (p2023b4-set-nonempty-p carrier set)
      (p2023b4-bounded-above-p carrier lt set))
     (p2023b4-has-supremum-p carrier lt set))))

(defun p2023b4-real-field-p
    (carrier zero one add mul neg inv lt)
  (and
   (tamep-functionp carrier)
   (tamep-functionp add)
   (tamep-functionp mul)
   (tamep-functionp neg)
   (tamep-functionp inv)
   (tamep-functionp lt)
   (p2023b4-member-p carrier zero)
   (p2023b4-member-p carrier one)
   (not (equal zero one))
   (p2023b4-field-laws-p
    carrier zero one add mul neg inv)
   (p2023b4-order-laws-p carrier zero add mul lt)
   (p2023b4-lt lt zero one)
   (p2023b4-dedekind-complete-p carrier lt)))

(defun-sk p2023b4-natural-real-function-p (carrier function)
  (forall (n)
    (implies
     (natp n)
     (p2023b4-member-p
      carrier (p2023b4-call1 function n)))))

(defun-sk p2023b4-real-function-p (carrier function)
  (forall (x)
    (implies
     (p2023b4-member-p carrier x)
     (p2023b4-member-p
      carrier (p2023b4-call1 function x)))))

(defun-sk p2023b4-spaced-times-p
    (one add lt times n)
  (forall (k)
    (implies
     (and (natp k) (< k n))
     (p2023b4-le
      lt
      (p2023b4-add
       add (p2023b4-call1 times k) one)
      (p2023b4-call1 times (+ k 1))))))

(defun p2023b4-domain-point-p (carrier lt times x)
  (and
   (p2023b4-member-p carrier x)
   (p2023b4-le lt (p2023b4-call1 times 0) x)))

(defun-sk p2023b4-continuity-ball-p
    (carrier zero add neg lt times function x epsilon delta)
  (forall (y)
    (implies
     (and
      (p2023b4-domain-point-p carrier lt times y)
      (p2023b4-lt
       lt
       (p2023b4-abs
        zero neg lt (p2023b4-sub add neg y x))
       delta))
     (p2023b4-lt
      lt
      (p2023b4-abs
       zero neg lt
       (p2023b4-sub
        add neg
        (p2023b4-call1 function y)
        (p2023b4-call1 function x)))
      epsilon))))

(defun-sk p2023b4-continuity-delta-exists-p
    (carrier zero add neg lt times function x epsilon)
  (exists (delta)
    (and
     (p2023b4-positive-p carrier zero lt delta)
     (p2023b4-continuity-ball-p
      carrier zero add neg lt times function
      x epsilon delta))))

(defun-sk p2023b4-continuous-at-on-domain-p
    (carrier zero add neg lt times function x)
  (forall (epsilon)
    (implies
     (p2023b4-positive-p carrier zero lt epsilon)
     (p2023b4-continuity-delta-exists-p
      carrier zero add neg lt times function x epsilon))))

(defun-sk p2023b4-continuous-on-domain-p
    (carrier zero add neg lt times function)
  (forall (x)
    (implies
     (p2023b4-domain-point-p carrier lt times x)
     (p2023b4-continuous-at-on-domain-p
      carrier zero add neg lt times function x))))

(defun p2023b4-no-reset-through-p (times x k)
  (declare (xargs :measure (nfix k)))
  (if (zp k)
      t
    (and
     (not (equal x (p2023b4-call1 times k)))
     (p2023b4-no-reset-through-p times x (- k 1)))))

(defun p2023b4-smooth-point-p
    (carrier lt times n x)
  (and
   (p2023b4-member-p carrier x)
   (p2023b4-lt lt (p2023b4-call1 times 0) x)
   (p2023b4-no-reset-through-p times x n)))

(defun p2023b4-difference-quotient
    (add mul neg inv function x h)
  (p2023b4-mul
   mul
   (p2023b4-sub
    add neg
    (p2023b4-call1
     function (p2023b4-add add x h))
    (p2023b4-call1 function x))
   (p2023b4-call1 inv h)))

(defun-sk p2023b4-derivative-ball-p
    (carrier zero add mul neg inv lt
     function x derivative epsilon delta)
  (forall (h)
    (implies
     (and
      (p2023b4-member-p carrier h)
      (p2023b4-lt
       lt zero (p2023b4-abs zero neg lt h))
      (p2023b4-lt
       lt (p2023b4-abs zero neg lt h) delta))
     (p2023b4-lt
      lt
      (p2023b4-abs
       zero neg lt
       (p2023b4-sub
        add neg
        (p2023b4-difference-quotient
         add mul neg inv function x h)
        derivative))
      epsilon))))

(defun-sk p2023b4-derivative-delta-exists-p
    (carrier zero add mul neg inv lt
     function x derivative epsilon)
  (exists (delta)
    (and
     (p2023b4-positive-p carrier zero lt delta)
     (p2023b4-derivative-ball-p
      carrier zero add mul neg inv lt
      function x derivative epsilon delta))))

(defun-sk p2023b4-derivative-at-p
    (carrier zero add mul neg inv lt
     function x derivative)
  (forall (epsilon)
    (implies
     (p2023b4-positive-p carrier zero lt epsilon)
     (p2023b4-derivative-delta-exists-p
      carrier zero add mul neg inv lt
      function x derivative epsilon))))

(defun-sk p2023b4-first-derivative-p
    (carrier zero add mul neg inv lt
     times n function first-derivative)
  (forall (x)
    (implies
     (p2023b4-smooth-point-p carrier lt times n x)
     (p2023b4-derivative-at-p
      carrier zero add mul neg inv lt
      function x (p2023b4-call1 first-derivative x)))))

(defun-sk p2023b4-second-derivative-p
    (carrier zero add mul neg inv lt
     times n first-derivative second-derivative)
  (forall (x)
    (implies
     (p2023b4-smooth-point-p carrier lt times n x)
     (p2023b4-derivative-at-p
      carrier zero add mul neg inv lt
      first-derivative x
      (p2023b4-call1 second-derivative x)))))

(defun-sk p2023b4-right-limit-ball-p
    (carrier zero add neg lt function point epsilon delta)
  (forall (x)
    (implies
     (and
      (p2023b4-member-p carrier x)
      (p2023b4-lt
       lt zero (p2023b4-sub add neg x point))
      (p2023b4-lt
       lt (p2023b4-sub add neg x point) delta))
     (p2023b4-lt
      lt
      (p2023b4-abs
       zero neg lt (p2023b4-call1 function x))
      epsilon))))

(defun-sk p2023b4-right-limit-delta-exists-p
    (carrier zero add neg lt function point epsilon)
  (exists (delta)
    (and
     (p2023b4-positive-p carrier zero lt delta)
     (p2023b4-right-limit-ball-p
      carrier zero add neg lt function
      point epsilon delta))))

(defun-sk p2023b4-right-limit-zero-p
    (carrier zero add neg lt function point)
  (forall (epsilon)
    (implies
     (p2023b4-positive-p carrier zero lt epsilon)
     (p2023b4-right-limit-delta-exists-p
      carrier zero add neg lt function point epsilon))))

(defun-sk p2023b4-all-reset-limits-p
    (carrier zero add neg lt times n first-derivative)
  (forall (k)
    (implies
     (and (natp k) (<= k n))
     (p2023b4-right-limit-zero-p
      carrier zero add neg lt first-derivative
      (p2023b4-call1 times k)))))

(defun-sk p2023b4-interior-accelerations-p
    (carrier zero one add lt times n second-derivative)
  (forall (k x)
    (implies
     (and
      (natp k)
      (< k n)
      (p2023b4-member-p carrier x)
      (p2023b4-lt lt (p2023b4-call1 times k) x)
      (p2023b4-lt
       lt x (p2023b4-call1 times (+ k 1))))
     (equal
      (p2023b4-call1 second-derivative x)
      (p2023b4-nat-real (+ k 1) zero one add)))))

(defun-sk p2023b4-terminal-acceleration-p
    (carrier zero one add lt times n second-derivative)
  (forall (x)
    (implies
     (and
      (p2023b4-member-p carrier x)
      (p2023b4-lt lt (p2023b4-call1 times n) x))
     (equal
      (p2023b4-call1 second-derivative x)
      (p2023b4-nat-real (+ n 1) zero one add)))))

(defun-sk p2023b4-feasible-time-p
    (elapsed carrier zero one add mul neg inv lt)
  (exists (n times function first-derivative second-derivative)
    (and
     (natp n)
     (tamep-functionp times)
     (tamep-functionp function)
     (tamep-functionp first-derivative)
     (tamep-functionp second-derivative)
     (p2023b4-member-p carrier elapsed)
     (p2023b4-le lt zero elapsed)
     (p2023b4-natural-real-function-p carrier times)
     (p2023b4-real-function-p carrier function)
     (p2023b4-real-function-p carrier first-derivative)
     (p2023b4-real-function-p carrier second-derivative)
     (p2023b4-spaced-times-p one add lt times n)
     (p2023b4-continuous-on-domain-p
      carrier zero add neg lt times function)
     (p2023b4-first-derivative-p
      carrier zero add mul neg inv lt
      times n function first-derivative)
     (p2023b4-second-derivative-p
      carrier zero add mul neg inv lt
      times n first-derivative second-derivative)
     (equal
      (p2023b4-call1 function (p2023b4-call1 times 0))
      (p2023b4-one-half one add mul inv))
     (p2023b4-all-reset-limits-p
      carrier zero add neg lt times n first-derivative)
     (p2023b4-interior-accelerations-p
      carrier zero one add lt times n second-derivative)
     (p2023b4-terminal-acceleration-p
      carrier zero one add lt times n second-derivative)
     (equal
      (p2023b4-call1
       function
       (p2023b4-add
        add (p2023b4-call1 times 0) elapsed))
      (p2023b4-nat-real 2023 zero one add)))))

(defun-sk p2023b4-all-feasible-times-at-least-p
    (minimum carrier zero one add mul neg inv lt)
  (forall (elapsed)
    (implies
     (p2023b4-feasible-time-p
      elapsed carrier zero one add mul neg inv lt)
     (p2023b4-le lt minimum elapsed))))

(defun putnambench-putnam-2023-b4-statement
    (carrier zero one add mul neg inv lt)
  (implies
   (p2023b4-real-field-p
    carrier zero one add mul neg inv lt)
   (let ((solution
          (p2023b4-nat-real 29 zero one add)))
     (and
      (p2023b4-feasible-time-p
       solution carrier zero one add mul neg inv lt)
      (p2023b4-all-feasible-times-at-least-p
       solution carrier zero one add mul neg inv lt)))))

(value-triple :itpeval-statement-checked)
:q
