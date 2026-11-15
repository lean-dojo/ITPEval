;; Statement-only formalization of PutnamBench corpus artifact putnam_1966_a5:
;; every local real-linear endomorphism of the continuous real-valued
;; functions on the real line is pointwise multiplication by a continuous
;; function. This file contains no proof.

(in-package "ACL2")

(set-inhibit-output-lst '(prove proof-tree event summary))

;; A Dedekind-complete ordered field presents the real numbers. Continuous
;; functions and T are APPLY$ function objects, and DEFUN-SK keeps all source
;; quantifiers internal to the statement predicates. Locality is stated on
;; every bounded closed interval, including singleton intervals, exactly as in
;; the canonical source statement.

(defun putnam-1966-a5-quoted (object)
  (list 'quote object))

(defun putnam-1966-a5-term-list (terms)
  (if (consp terms)
      (list 'cons
            (car terms)
            (putnam-1966-a5-term-list (cdr terms)))
    (putnam-1966-a5-quoted nil)))

(defun putnam-1966-a5-apply-term (function arguments)
  (list 'apply$
        (putnam-1966-a5-quoted function)
        (putnam-1966-a5-term-list arguments)))

(defun putnam-1966-a5-member-p (carrier x)
  (if (apply$ carrier (list x)) t nil))

(defun putnam-1966-a5-unary (operation x)
  (apply$ operation (list x)))

(defun putnam-1966-a5-binary (operation x y)
  (apply$ operation (list x y)))

(defun putnam-1966-a5-function-value (function x)
  (apply$ function (list x)))

(defun putnam-1966-a5-operator-value (operator function)
  (apply$ operator (list function)))

(defun putnam-1966-a5-positive-p (carrier zero less x)
  (and
   (putnam-1966-a5-member-p carrier x)
   (apply$ less (list zero x))))

(defun putnam-1966-a5-absolute-value
    (zero negate less x)
  (if (apply$ less (list x zero))
      (putnam-1966-a5-unary negate x)
    x))

(defun putnam-1966-a5-distance
    (zero add negate less x y)
  (putnam-1966-a5-absolute-value
   zero negate less
   (putnam-1966-a5-binary
    add x (putnam-1966-a5-unary negate y))))

(defun-sk putnam-1966-a5-field-laws-p
    (carrier zero one add multiply negate inverse)
  (forall (x y z)
    (implies
     (and
      (putnam-1966-a5-member-p carrier x)
      (putnam-1966-a5-member-p carrier y)
      (putnam-1966-a5-member-p carrier z))
     (and
      (putnam-1966-a5-member-p
       carrier (putnam-1966-a5-binary add x y))
      (putnam-1966-a5-member-p
       carrier (putnam-1966-a5-binary multiply x y))
      (putnam-1966-a5-member-p
       carrier (putnam-1966-a5-unary negate x))
      (putnam-1966-a5-member-p
       carrier (putnam-1966-a5-unary inverse x))
      (equal
       (putnam-1966-a5-binary
        add (putnam-1966-a5-binary add x y) z)
       (putnam-1966-a5-binary
        add x (putnam-1966-a5-binary add y z)))
      (equal
       (putnam-1966-a5-binary add x y)
       (putnam-1966-a5-binary add y x))
      (equal (putnam-1966-a5-binary add x zero) x)
      (equal
       (putnam-1966-a5-binary
        add x (putnam-1966-a5-unary negate x))
       zero)
      (equal
       (putnam-1966-a5-binary
        multiply (putnam-1966-a5-binary multiply x y) z)
       (putnam-1966-a5-binary
        multiply x (putnam-1966-a5-binary multiply y z)))
      (equal
       (putnam-1966-a5-binary multiply x y)
       (putnam-1966-a5-binary multiply y x))
      (equal (putnam-1966-a5-binary multiply x one) x)
      (equal (putnam-1966-a5-unary inverse zero) zero)
      (implies
       (not (equal x zero))
       (equal
        (putnam-1966-a5-binary
         multiply x (putnam-1966-a5-unary inverse x))
        one))
      (equal
       (putnam-1966-a5-binary
        multiply x (putnam-1966-a5-binary add y z))
       (putnam-1966-a5-binary
        add
        (putnam-1966-a5-binary multiply x y)
        (putnam-1966-a5-binary multiply x z)))))))

(defun-sk putnam-1966-a5-order-laws-p
    (carrier zero add multiply less)
  (forall (x y z)
    (implies
     (and
      (putnam-1966-a5-member-p carrier x)
      (putnam-1966-a5-member-p carrier y)
      (putnam-1966-a5-member-p carrier z))
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
         (putnam-1966-a5-binary add x z)
         (putnam-1966-a5-binary add y z))))
      (implies
       (and
        (apply$ less (list zero x))
        (apply$ less (list zero y)))
       (apply$
        less
        (list zero
              (putnam-1966-a5-binary multiply x y))))))))

(defun-sk putnam-1966-a5-set-nonempty-p (carrier set)
  (exists (x)
    (and
     (putnam-1966-a5-member-p carrier x)
     (apply$ set (list x)))))

(defun-sk putnam-1966-a5-upper-bound-p
    (carrier less set bound)
  (forall (x)
    (implies
     (and
      (putnam-1966-a5-member-p carrier x)
      (apply$ set (list x)))
     (not (apply$ less (list bound x))))))

(defun-sk putnam-1966-a5-bounded-above-p
    (carrier less set)
  (exists (bound)
    (and
     (putnam-1966-a5-member-p carrier bound)
     (putnam-1966-a5-upper-bound-p
      carrier less set bound))))

(defun-sk putnam-1966-a5-supremum-p
    (carrier less set supremum)
  (forall (bound)
    (and
     (putnam-1966-a5-member-p carrier supremum)
     (putnam-1966-a5-upper-bound-p
      carrier less set supremum)
     (implies
      (and
       (putnam-1966-a5-member-p carrier bound)
       (putnam-1966-a5-upper-bound-p
        carrier less set bound))
      (not (apply$ less (list bound supremum)))))))

(defun-sk putnam-1966-a5-has-supremum-p
    (carrier less set)
  (exists (supremum)
    (putnam-1966-a5-supremum-p
     carrier less set supremum)))

(defun-sk putnam-1966-a5-dedekind-complete-p
    (carrier less)
  (forall (set)
    (implies
     (and
      (tamep-functionp set)
      (putnam-1966-a5-set-nonempty-p carrier set)
      (putnam-1966-a5-bounded-above-p carrier less set))
     (putnam-1966-a5-has-supremum-p
      carrier less set))))

(defun putnam-1966-a5-real-field-p
    (carrier zero one add multiply negate inverse less)
  (and
   (tamep-functionp carrier)
   (tamep-functionp add)
   (tamep-functionp multiply)
   (tamep-functionp negate)
   (tamep-functionp inverse)
   (tamep-functionp less)
   (putnam-1966-a5-member-p carrier zero)
   (putnam-1966-a5-member-p carrier one)
   (not (equal zero one))
   (putnam-1966-a5-field-laws-p
    carrier zero one add multiply negate inverse)
   (putnam-1966-a5-order-laws-p
    carrier zero add multiply less)
   (apply$ less (list zero one))
   (putnam-1966-a5-dedekind-complete-p carrier less)))

(defun-sk putnam-1966-a5-function-typing-p
    (carrier function)
  (forall (x)
    (implies
     (putnam-1966-a5-member-p carrier x)
     (putnam-1966-a5-member-p
      carrier
      (putnam-1966-a5-function-value function x)))))

(defun putnam-1966-a5-function-p (carrier function)
  (and
   (tamep-functionp function)
   (putnam-1966-a5-function-typing-p carrier function)))

(defun-sk putnam-1966-a5-continuous-at-delta-p
    (carrier zero add negate less function x epsilon delta)
  (forall (y)
    (implies
     (and
      (putnam-1966-a5-member-p carrier y)
      (apply$
       less
       (list
        (putnam-1966-a5-distance
         zero add negate less y x)
        delta)))
     (apply$
      less
      (list
       (putnam-1966-a5-distance
        zero add negate less
        (putnam-1966-a5-function-value function y)
        (putnam-1966-a5-function-value function x))
       epsilon)))))

(defun-sk putnam-1966-a5-continuous-at-p
    (carrier zero add negate less function x epsilon)
  (exists (delta)
    (and
     (putnam-1966-a5-positive-p carrier zero less delta)
     (putnam-1966-a5-continuous-at-delta-p
      carrier zero add negate less
      function x epsilon delta))))

(defun-sk putnam-1966-a5-continuity-p
    (carrier zero add negate less function)
  (forall (x epsilon)
    (implies
     (and
      (putnam-1966-a5-member-p carrier x)
      (putnam-1966-a5-positive-p carrier zero less epsilon))
     (putnam-1966-a5-continuous-at-p
      carrier zero add negate less function x epsilon))))

(defun putnam-1966-a5-continuous-function-p
    (carrier zero add negate less function)
  (and
   (putnam-1966-a5-function-p carrier function)
   (putnam-1966-a5-continuity-p
    carrier zero add negate less function)))

(defun-sk putnam-1966-a5-functions-equal-p
    (carrier left right)
  (forall (x)
    (implies
     (putnam-1966-a5-member-p carrier x)
     (equal
      (putnam-1966-a5-function-value left x)
      (putnam-1966-a5-function-value right x)))))

(defun putnam-1966-a5-linear-combination-function
    (add multiply a b f g)
  (let ((fx (putnam-1966-a5-apply-term f '(x)))
        (gx (putnam-1966-a5-apply-term g '(x))))
    (list
     'lambda
     '(x)
     (putnam-1966-a5-apply-term
      add
      (list
       (putnam-1966-a5-apply-term
        multiply
        (list (putnam-1966-a5-quoted a) fx))
       (putnam-1966-a5-apply-term
        multiply
        (list (putnam-1966-a5-quoted b) gx)))))))

(defun putnam-1966-a5-product-function
    (multiply f g)
  (list
   'lambda
   '(x)
   (putnam-1966-a5-apply-term
    multiply
    (list
     (putnam-1966-a5-apply-term f '(x))
     (putnam-1966-a5-apply-term g '(x))))))

(defun-sk putnam-1966-a5-image-p
    (carrier zero add negate less operator)
  (forall (f)
    (implies
     (putnam-1966-a5-continuous-function-p
      carrier zero add negate less f)
     (putnam-1966-a5-continuous-function-p
      carrier zero add negate less
      (putnam-1966-a5-operator-value operator f)))))

(defun-sk putnam-1966-a5-linearity-p
    (carrier zero add multiply negate less operator)
  (forall (a b f g)
    (implies
     (and
      (putnam-1966-a5-member-p carrier a)
      (putnam-1966-a5-member-p carrier b)
      (putnam-1966-a5-continuous-function-p
       carrier zero add negate less f)
      (putnam-1966-a5-continuous-function-p
       carrier zero add negate less g))
     (putnam-1966-a5-functions-equal-p
      carrier
      (putnam-1966-a5-operator-value
       operator
       (putnam-1966-a5-linear-combination-function
        add multiply a b f g))
      (putnam-1966-a5-linear-combination-function
       add multiply a b
       (putnam-1966-a5-operator-value operator f)
       (putnam-1966-a5-operator-value operator g))))))

(defun-sk putnam-1966-a5-agree-on-interval-p
    (carrier less f g r s)
  (forall (x)
    (implies
     (and
      (putnam-1966-a5-member-p carrier x)
      (not (apply$ less (list x r)))
      (not (apply$ less (list s x))))
     (equal
      (putnam-1966-a5-function-value f x)
      (putnam-1966-a5-function-value g x)))))

(defun-sk putnam-1966-a5-locality-p
    (carrier zero add negate less operator)
  (forall (r s f g)
    (implies
     (and
      (putnam-1966-a5-member-p carrier r)
      (putnam-1966-a5-member-p carrier s)
      (not (apply$ less (list s r)))
      (putnam-1966-a5-continuous-function-p
       carrier zero add negate less f)
      (putnam-1966-a5-continuous-function-p
       carrier zero add negate less g)
      (putnam-1966-a5-agree-on-interval-p
       carrier less f g r s))
     (putnam-1966-a5-agree-on-interval-p
      carrier less
      (putnam-1966-a5-operator-value operator f)
      (putnam-1966-a5-operator-value operator g)
      r s))))

(defun-sk putnam-1966-a5-multiplier-p
    (carrier zero add multiply negate less operator multiplier)
  (forall (g)
    (implies
     (putnam-1966-a5-continuous-function-p
      carrier zero add negate less g)
     (putnam-1966-a5-functions-equal-p
      carrier
      (putnam-1966-a5-operator-value operator g)
      (putnam-1966-a5-product-function
       multiply multiplier g)))))

(defun-sk putnam-1966-a5-conclusion-p
    (carrier zero add multiply negate less operator)
  (exists (multiplier)
    (and
     (putnam-1966-a5-continuous-function-p
      carrier zero add negate less multiplier)
     (putnam-1966-a5-multiplier-p
      carrier zero add multiply negate less
      operator multiplier))))

(defun putnambench-putnam-1966-a5-statement
    (carrier zero one add multiply negate inverse less operator)
  (implies
   (and
    (putnam-1966-a5-real-field-p
     carrier zero one add multiply negate inverse less)
    (tamep-functionp operator)
    (putnam-1966-a5-image-p
     carrier zero add negate less operator)
    (putnam-1966-a5-linearity-p
     carrier zero add multiply negate less operator)
    (putnam-1966-a5-locality-p
     carrier zero add negate less operator))
   (putnam-1966-a5-conclusion-p
    carrier zero add multiply negate less operator)))

(value-triple :itpeval-statement-checked)
:q
