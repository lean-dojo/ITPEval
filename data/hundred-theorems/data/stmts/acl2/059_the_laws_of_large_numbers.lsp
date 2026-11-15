;; Statement-only formalization of hundred-theorems corpus artifact
;; hundred-theorems__acl2__059, "The Laws of Large Numbers": pairwise
;; independent, identically distributed, integrable real random variables
;; have sample averages converging almost surely to their common expectation.
;; This file contains no proof.
;;
;; Semantic status: the direct DEFUN-SK rewrite below repairs the former
;; vacuous generated-lambda quantifiers, but standard ACL2 still ranges only
;; over coded events, random variables, and scalar values. It cannot preserve
;; the source's unrestricted real probability-space semantics and is not
;; counted as a faithful translation.

(in-package "ACL2")

(set-inhibit-output-lst '(prove proof-tree event summary))

;; Function objects present the scalar operations, event operations, and
;; random-variable family. All mathematical quantifiers below are DEFUN-SK
;; quantifiers over ordinary ACL2 objects; no generated lambda calls an
;; unwarranted user function.

(defun ht059-apply1 (function x)
  (apply$ function (list x)))

(defun ht059-apply2 (function x y)
  (apply$ function (list x y)))

(defun ht059-apply3 (function x y z)
  (apply$ function (list x y z)))

(defun ht059-scalar-p (carrier x)
  (if (ht059-apply1 carrier x) t nil))

(defun ht059-sample-p (sample-carrier omega)
  (if (ht059-apply1 sample-carrier omega) t nil))

(defun ht059-less-p (less x y)
  (if (ht059-apply2 less x y) t nil))

(defun ht059-leq-p (less x y)
  (not (ht059-less-p less y x)))

(defun ht059-add (add x y)
  (ht059-apply2 add x y))

(defun ht059-mul (multiply x y)
  (ht059-apply2 multiply x y))

(defun ht059-neg (negate x)
  (ht059-apply1 negate x))

(defun ht059-sub (add negate x y)
  (ht059-add add x (ht059-neg negate y)))

(defun ht059-inv (inverse x)
  (ht059-apply1 inverse x))

(defun ht059-div (multiply inverse x y)
  (ht059-mul multiply x (ht059-inv inverse y)))

(defun ht059-abs (less negate zero x)
  (if (ht059-less-p less x zero)
      (ht059-neg negate x)
    x))

(defun ht059-max (less x y)
  (if (ht059-less-p less x y) y x))

(defun ht059-real-nat (add zero one n)
  (declare (xargs :measure (nfix n)))
  (if (zp n)
      zero
    (ht059-add
     add one
     (ht059-real-nat add zero one (1- n)))))

;; The scalar carrier is an Archimedean Dedekind-complete ordered field.

(defun-sk ht059-field-laws-p
    (carrier zero one add multiply negate inverse)
  (forall (x y z)
    (implies
     (and
      (ht059-scalar-p carrier x)
      (ht059-scalar-p carrier y)
      (ht059-scalar-p carrier z))
     (and
      (ht059-scalar-p carrier (ht059-add add x y))
      (ht059-scalar-p carrier (ht059-mul multiply x y))
      (ht059-scalar-p carrier (ht059-neg negate x))
      (ht059-scalar-p carrier (ht059-inv inverse x))
      (equal
       (ht059-add add (ht059-add add x y) z)
       (ht059-add add x (ht059-add add y z)))
      (equal (ht059-add add x y) (ht059-add add y x))
      (equal (ht059-add add x zero) x)
      (equal (ht059-add add x (ht059-neg negate x)) zero)
      (equal
       (ht059-mul multiply (ht059-mul multiply x y) z)
       (ht059-mul multiply x (ht059-mul multiply y z)))
      (equal (ht059-mul multiply x y) (ht059-mul multiply y x))
      (equal (ht059-mul multiply x one) x)
      (implies
       (equal x zero)
       (equal (ht059-inv inverse x) zero))
      (implies
       (not (equal x zero))
       (equal (ht059-mul multiply x (ht059-inv inverse x)) one))
      (equal
       (ht059-mul multiply x (ht059-add add y z))
       (ht059-add
        add
        (ht059-mul multiply x y)
        (ht059-mul multiply x z)))))))

(defun-sk ht059-order-laws-p
    (carrier zero add multiply less)
  (forall (x y z)
    (implies
     (and
      (ht059-scalar-p carrier x)
      (ht059-scalar-p carrier y)
      (ht059-scalar-p carrier z))
     (and
      (not (ht059-less-p less x x))
      (or
       (equal x y)
       (ht059-less-p less x y)
       (ht059-less-p less y x))
      (implies
       (and
        (ht059-less-p less x y)
        (ht059-less-p less y z))
       (ht059-less-p less x z))
      (implies
       (ht059-less-p less x y)
       (ht059-less-p
        less
        (ht059-add add x z)
        (ht059-add add y z)))
      (implies
       (and
        (ht059-less-p less zero x)
        (ht059-less-p less zero y))
       (ht059-less-p less zero (ht059-mul multiply x y)))))))

(defun-sk ht059-real-set-nonempty-p (carrier set)
  (exists (x)
    (and
     (ht059-scalar-p carrier x)
     (ht059-apply1 set x))))

(defun-sk ht059-real-set-upper-bound-p (carrier less set bound)
  (forall (x)
    (implies
     (and
      (ht059-scalar-p carrier x)
      (ht059-apply1 set x))
     (ht059-leq-p less x bound))))

(defun-sk ht059-real-set-bounded-above-p (carrier less set)
  (exists (bound)
    (and
     (ht059-scalar-p carrier bound)
     (ht059-real-set-upper-bound-p carrier less set bound))))

(defun-sk ht059-real-set-least-upper-bound-p
    (carrier less set supremum)
  (forall (bound)
    (implies
     (and
      (ht059-scalar-p carrier bound)
      (ht059-real-set-upper-bound-p carrier less set bound))
     (ht059-leq-p less supremum bound))))

(defun ht059-real-set-supremum-p
    (carrier less set supremum)
  (and
   (ht059-scalar-p carrier supremum)
   (ht059-real-set-upper-bound-p carrier less set supremum)
   (ht059-real-set-least-upper-bound-p
    carrier less set supremum)))

(defun-sk ht059-real-set-has-supremum-p (carrier less set)
  (exists (supremum)
    (ht059-real-set-supremum-p
     carrier less set supremum)))

(defun-sk ht059-dedekind-complete-p (carrier less)
  (forall (set)
    (implies
     (and
      (tamep-functionp set)
      (ht059-real-set-nonempty-p carrier set)
      (ht059-real-set-bounded-above-p carrier less set))
     (ht059-real-set-has-supremum-p carrier less set))))

(defun-sk ht059-archimedean-witness-p
    (carrier add zero one less x)
  (exists (n)
    (and
     (natp n)
     (ht059-less-p
      less x (ht059-real-nat add zero one n)))))

(defun-sk ht059-archimedean-p
    (carrier add zero one less)
  (forall (x)
    (implies
     (ht059-scalar-p carrier x)
     (ht059-archimedean-witness-p
      carrier add zero one less x))))

(defun ht059-real-field-p
    (carrier zero one add multiply negate inverse less)
  (and
   (tamep-functionp carrier)
   (tamep-functionp add)
   (tamep-functionp multiply)
   (tamep-functionp negate)
   (tamep-functionp inverse)
   (tamep-functionp less)
   (ht059-scalar-p carrier zero)
   (ht059-scalar-p carrier one)
   (not (equal zero one))
   (ht059-less-p less zero one)
   (ht059-field-laws-p
    carrier zero one add multiply negate inverse)
   (ht059-order-laws-p
    carrier zero add multiply less)
   (ht059-dedekind-complete-p carrier less)
   (ht059-archimedean-p carrier add zero one less)))

;; Events are first-order event codes with an explicit membership relation.
;; The closure operations state their extensional meaning, so no event is
;; represented by a generated lambda.

(defun ht059-event-p (events event)
  (if (ht059-apply1 events event) t nil))

(defun ht059-in-event-p (event-member event omega)
  (if (ht059-apply2 event-member event omega) t nil))

(defun ht059-sequence-event
    (sequence-value sequence index)
  (ht059-apply2 sequence-value sequence index))

(defun-sk ht059-events-contained-p
    (sample-carrier events event-member)
  (forall (event omega)
    (implies
     (and
      (ht059-event-p events event)
      (ht059-in-event-p event-member event omega))
     (ht059-sample-p sample-carrier omega))))

(defun-sk ht059-empty-full-events-p
    (sample-carrier event-member empty-event full-event)
  (forall (omega)
    (implies
     (ht059-sample-p sample-carrier omega)
     (and
      (not
       (ht059-in-event-p event-member empty-event omega))
      (ht059-in-event-p event-member full-event omega)))))

(defun-sk ht059-complement-closure-p
    (events complement-event)
  (forall (event)
    (implies
     (ht059-event-p events event)
     (ht059-event-p
      events (ht059-apply1 complement-event event)))))

(defun-sk ht059-complement-membership-p
    (sample-carrier events event-member complement-event)
  (forall (event omega)
    (implies
     (and
      (ht059-event-p events event)
      (ht059-sample-p sample-carrier omega))
     (iff
      (ht059-in-event-p
       event-member
       (ht059-apply1 complement-event event)
       omega)
      (not (ht059-in-event-p event-member event omega))))))

(defun-sk ht059-intersection-closure-p
    (events intersection-event)
  (forall (left right)
    (implies
     (and
      (ht059-event-p events left)
      (ht059-event-p events right))
     (ht059-event-p
      events
      (ht059-apply2 intersection-event left right)))))

(defun-sk ht059-intersection-membership-p
    (sample-carrier events event-member intersection-event)
  (forall (left right omega)
    (implies
     (and
      (ht059-event-p events left)
      (ht059-event-p events right)
      (ht059-sample-p sample-carrier omega))
     (iff
      (ht059-in-event-p
       event-member
       (ht059-apply2 intersection-event left right)
       omega)
      (and
       (ht059-in-event-p event-member left omega)
       (ht059-in-event-p event-member right omega))))))

(defun-sk ht059-event-sequence-p
    (events sequence-value sequence)
  (forall (index)
    (implies
     (natp index)
     (ht059-event-p
      events
      (ht059-sequence-event
       sequence-value sequence index)))))

(defun-sk ht059-point-in-sequence-union-p
    (sequence-value event-member sequence omega)
  (exists (index)
    (and
     (natp index)
     (ht059-in-event-p
      event-member
      (ht059-sequence-event
       sequence-value sequence index)
      omega))))

(defun-sk ht059-countable-union-closure-p
    (events sequence-value countable-union-event)
  (forall (sequence)
    (implies
     (ht059-event-sequence-p events sequence-value sequence)
     (ht059-event-p
      events
      (ht059-apply1 countable-union-event sequence)))))

(defun-sk ht059-countable-union-membership-p
    (sample-carrier events event-member sequence-value
                    countable-union-event)
  (forall (sequence omega)
    (implies
     (and
      (ht059-event-sequence-p
       events sequence-value sequence)
      (ht059-sample-p sample-carrier omega))
     (iff
      (ht059-in-event-p
       event-member
       (ht059-apply1 countable-union-event sequence)
       omega)
      (ht059-point-in-sequence-union-p
       sequence-value event-member sequence omega)))))

(defun ht059-sigma-algebra-p
    (sample-carrier events event-member empty-event full-event
                    complement-event intersection-event
                    sequence-value countable-union-event)
  (and
   (tamep-functionp sample-carrier)
   (tamep-functionp events)
   (tamep-functionp event-member)
   (tamep-functionp complement-event)
   (tamep-functionp intersection-event)
   (tamep-functionp sequence-value)
   (tamep-functionp countable-union-event)
   (ht059-event-p events empty-event)
   (ht059-event-p events full-event)
   (ht059-events-contained-p
    sample-carrier events event-member)
   (ht059-empty-full-events-p
    sample-carrier event-member empty-event full-event)
   (ht059-complement-closure-p events complement-event)
   (ht059-complement-membership-p
    sample-carrier events event-member complement-event)
   (ht059-intersection-closure-p events intersection-event)
   (ht059-intersection-membership-p
    sample-carrier events event-member intersection-event)
   (ht059-countable-union-closure-p
    events sequence-value countable-union-event)
   (ht059-countable-union-membership-p
    sample-carrier events event-member sequence-value
    countable-union-event)))

(defun-sk ht059-events-equivalent-p
    (sample-carrier event-member left right)
  (forall (omega)
    (implies
     (ht059-sample-p sample-carrier omega)
     (iff
      (ht059-in-event-p event-member left omega)
      (ht059-in-event-p event-member right omega)))))

(defun-sk ht059-measure-extensional-p
    (sample-carrier events event-member measure)
  (forall (left right)
    (implies
     (and
      (ht059-event-p events left)
      (ht059-event-p events right)
      (ht059-events-equivalent-p
       sample-carrier event-member left right))
     (equal
      (ht059-apply1 measure left)
      (ht059-apply1 measure right)))))

(defun-sk ht059-measure-values-p
    (carrier zero less events measure)
  (forall (event)
    (implies
     (ht059-event-p events event)
     (and
      (ht059-scalar-p
       carrier (ht059-apply1 measure event))
      (ht059-leq-p
       less zero (ht059-apply1 measure event))))))

(defun-sk ht059-events-disjoint-p
    (sample-carrier event-member left right)
  (forall (omega)
    (implies
     (ht059-sample-p sample-carrier omega)
     (not
      (and
       (ht059-in-event-p event-member left omega)
       (ht059-in-event-p event-member right omega))))))

(defun-sk ht059-event-sequence-pairwise-disjoint-p
    (sample-carrier event-member sequence-value sequence)
  (forall (left-index right-index)
    (implies
     (and
      (natp left-index)
      (natp right-index)
      (not (equal left-index right-index)))
     (ht059-events-disjoint-p
      sample-carrier event-member
      (ht059-sequence-event
       sequence-value sequence left-index)
      (ht059-sequence-event
       sequence-value sequence right-index)))))

(defun ht059-measure-prefix
    (measure sequence-value sequence add zero count)
  (declare (xargs :measure (nfix count)))
  (if (zp count)
      zero
    (let ((index (1- count)))
      (ht059-add
       add
       (ht059-measure-prefix
        measure sequence-value sequence add zero index)
       (ht059-apply1
        measure
        (ht059-sequence-event
         sequence-value sequence index))))))

(defun-sk ht059-measure-prefix-tail-p
    (measure sequence-value sequence total
             add negate zero less epsilon cutoff)
  (forall (count)
    (implies
     (and
      (natp count)
      (natp cutoff)
      (<= cutoff count))
     (ht059-less-p
      less
      (ht059-abs
       less negate zero
       (ht059-sub
        add negate
        (ht059-measure-prefix
         measure sequence-value sequence add zero count)
        total))
      epsilon))))

(defun-sk ht059-measure-prefix-cutoff-exists-p
    (measure sequence-value sequence total
             add negate zero less epsilon)
  (exists (cutoff)
    (and
     (natp cutoff)
     (ht059-measure-prefix-tail-p
      measure sequence-value sequence total
      add negate zero less epsilon cutoff))))

(defun-sk ht059-measure-prefix-converges-p
    (carrier measure sequence-value sequence total
             add negate zero less)
  (forall (epsilon)
    (implies
     (and
      (ht059-scalar-p carrier epsilon)
      (ht059-less-p less zero epsilon))
     (ht059-measure-prefix-cutoff-exists-p
      measure sequence-value sequence total
      add negate zero less epsilon))))

(defun-sk ht059-countable-additivity-p
    (carrier add negate zero less
             sample-carrier events event-member
             sequence-value countable-union-event measure)
  (forall (sequence)
    (implies
     (and
      (ht059-event-sequence-p
       events sequence-value sequence)
      (ht059-event-sequence-pairwise-disjoint-p
       sample-carrier event-member sequence-value sequence))
     (ht059-measure-prefix-converges-p
      carrier measure sequence-value sequence
      (ht059-apply1
       measure
       (ht059-apply1 countable-union-event sequence))
      add negate zero less))))

(defun ht059-probability-space-p
    (carrier zero one add negate less
             sample-carrier events event-member
             empty-event full-event complement-event intersection-event
             sequence-value countable-union-event measure)
  (and
   (tamep-functionp measure)
   (ht059-sigma-algebra-p
    sample-carrier events event-member empty-event full-event
    complement-event intersection-event
    sequence-value countable-union-event)
   (ht059-measure-values-p
    carrier zero less events measure)
   (ht059-measure-extensional-p
    sample-carrier events event-member measure)
   (equal (ht059-apply1 measure empty-event) zero)
   (equal (ht059-apply1 measure full-event) one)
   (ht059-countable-additivity-p
    carrier add negate zero less
    sample-carrier events event-member
    sequence-value countable-union-event measure)))

;; Upper-ray events characterize measurability, equality in distribution,
;; and pairwise independence for real-valued random variables.

(defun-sk ht059-family-values-p
    (carrier sample-carrier x-family)
  (forall (index omega)
    (implies
     (and
      (natp index)
      (ht059-sample-p sample-carrier omega))
     (ht059-scalar-p
      carrier (ht059-apply2 x-family index omega)))))

(defun-sk ht059-ray-event-closure-p
    (carrier events ray-event)
  (forall (index threshold)
    (implies
     (and
      (natp index)
      (ht059-scalar-p carrier threshold))
     (ht059-event-p
      events (ht059-apply2 ray-event index threshold)))))

(defun-sk ht059-ray-event-membership-p
    (carrier sample-carrier event-member x-family ray-event less)
  (forall (index threshold omega)
    (implies
     (and
      (natp index)
      (ht059-scalar-p carrier threshold)
      (ht059-sample-p sample-carrier omega))
     (iff
      (ht059-in-event-p
       event-member
       (ht059-apply2 ray-event index threshold)
       omega)
      (ht059-less-p
       less
       (ht059-apply2 x-family index omega)
       threshold)))))

(defun-sk ht059-identically-distributed-p
    (carrier events measure ray-event)
  (forall (index threshold)
    (implies
     (and
      (natp index)
      (ht059-scalar-p carrier threshold)
      (ht059-event-p
       events (ht059-apply2 ray-event index threshold))
      (ht059-event-p
       events (ht059-apply2 ray-event 0 threshold)))
     (equal
      (ht059-apply1
       measure (ht059-apply2 ray-event index threshold))
      (ht059-apply1
       measure (ht059-apply2 ray-event 0 threshold))))))

(defun-sk ht059-pairwise-independent-p
    (carrier events intersection-event measure ray-event multiply)
  (forall (left-index right-index left-threshold right-threshold)
    (implies
     (and
      (natp left-index)
      (natp right-index)
      (not (equal left-index right-index))
      (ht059-scalar-p carrier left-threshold)
      (ht059-scalar-p carrier right-threshold)
      (ht059-event-p
       events
       (ht059-apply2 ray-event left-index left-threshold))
      (ht059-event-p
       events
       (ht059-apply2 ray-event right-index right-threshold)))
     (let* ((left-event
             (ht059-apply2
              ray-event left-index left-threshold))
            (right-event
             (ht059-apply2
              ray-event right-index right-threshold))
            (joint-event
             (ht059-apply2
              intersection-event left-event right-event)))
       (equal
        (ht059-apply1 measure joint-event)
        (ht059-mul
         multiply
         (ht059-apply1 measure left-event)
         (ht059-apply1 measure right-event)))))))

;; The positive and negative expectation parts are limits of the standard
;; dyadic lower sums
;;
;;   2^-n * sum_{1 <= k <= n*2^n} P(k/2^n <= Y).
;;
;; This directly characterizes the Lebesgue expectation of a nonnegative
;; random variable and avoids an uninterpreted integral operator.

(defun ht059-positive-part (less zero value)
  (ht059-max less zero value))

(defun ht059-negative-part (less negate zero value)
  (ht059-max less zero (ht059-neg negate value)))

(defun ht059-signed-part
    (positivep less negate zero value)
  (if positivep
      (ht059-positive-part less zero value)
    (ht059-negative-part less negate zero value)))

(defun-sk ht059-level-event-closure-p
    (carrier zero less events level-event)
  (forall (index positivep threshold)
    (implies
     (and
      (natp index)
      (booleanp positivep)
      (ht059-scalar-p carrier threshold)
      (ht059-leq-p less zero threshold))
     (ht059-event-p
      events
      (ht059-apply3
       level-event index positivep threshold)))))

(defun-sk ht059-level-event-membership-p
    (carrier sample-carrier event-member x-family level-event
             zero negate less)
  (forall (index positivep threshold omega)
    (implies
     (and
      (natp index)
      (booleanp positivep)
      (ht059-scalar-p carrier threshold)
      (ht059-leq-p less zero threshold)
      (ht059-sample-p sample-carrier omega))
     (iff
      (ht059-in-event-p
       event-member
       (ht059-apply3
        level-event index positivep threshold)
       omega)
      (ht059-leq-p
       less threshold
       (ht059-signed-part
        positivep less negate zero
        (ht059-apply2 x-family index omega)))))))

(defun ht059-dyadic-denominator (add multiply one exponent)
  (declare (xargs :measure (nfix exponent)))
  (if (zp exponent)
      one
    (ht059-mul
     multiply
     (ht059-add add one one)
     (ht059-dyadic-denominator
      add multiply one (1- exponent)))))

(defun ht059-level-measure-sum
    (measure level-event index positivep
             add multiply inverse zero one denominator count)
  (declare (xargs :measure (nfix count)))
  (if (zp count)
      zero
    (let* ((k (nfix count))
           (threshold
            (ht059-div
             multiply inverse
             (ht059-real-nat add zero one k)
             denominator)))
      (ht059-add
       add
       (ht059-level-measure-sum
        measure level-event index positivep
        add multiply inverse zero one denominator (1- count))
       (ht059-apply1
        measure
        (ht059-apply3
         level-event index positivep threshold))))))

(defun ht059-expectation-approximation
    (measure level-event index positivep n
             add multiply inverse zero one)
  (let* ((native-n (nfix n))
         (native-power (expt 2 native-n))
         (count (* native-n native-power))
         (denominator
          (ht059-dyadic-denominator
           add multiply one native-n)))
    (ht059-mul
     multiply
     (ht059-inv inverse denominator)
     (ht059-level-measure-sum
      measure level-event index positivep
      add multiply inverse zero one denominator count))))

(defun-sk ht059-expectation-limit-tail-p
    (measure level-event index positivep limit
             add multiply negate inverse zero one less
             epsilon cutoff)
  (forall (n)
    (implies
     (and
      (natp n)
      (natp cutoff)
      (<= cutoff n))
     (ht059-less-p
      less
      (ht059-abs
       less negate zero
       (ht059-sub
        add negate
        (ht059-expectation-approximation
         measure level-event index positivep n
         add multiply inverse zero one)
        limit))
      epsilon))))

(defun-sk ht059-expectation-limit-cutoff-exists-p
    (measure level-event index positivep limit
             add multiply negate inverse zero one less epsilon)
  (exists (cutoff)
    (and
     (natp cutoff)
     (ht059-expectation-limit-tail-p
      measure level-event index positivep limit
      add multiply negate inverse zero one less
      epsilon cutoff))))

(defun-sk ht059-nonnegative-expectation-limit-p
    (carrier measure level-event index positivep limit
             add multiply negate inverse zero one less)
  (forall (epsilon)
    (implies
     (and
      (ht059-scalar-p carrier epsilon)
      (ht059-less-p less zero epsilon))
     (ht059-expectation-limit-cutoff-exists-p
      measure level-event index positivep limit
      add multiply negate inverse zero one less epsilon))))

(defun ht059-nonnegative-expectation-p
    (carrier measure level-event index positivep limit
             add multiply negate inverse zero one less)
  (and
   (ht059-scalar-p carrier limit)
   (ht059-leq-p less zero limit)
   (ht059-nonnegative-expectation-limit-p
    carrier measure level-event index positivep limit
    add multiply negate inverse zero one less)))

(defun-sk ht059-has-expectation-p
    (carrier measure level-event index mean
             add multiply negate inverse zero one less)
  (exists (positive-expectation negative-expectation)
    (and
     (ht059-nonnegative-expectation-p
      carrier measure level-event index t positive-expectation
      add multiply negate inverse zero one less)
     (ht059-nonnegative-expectation-p
      carrier measure level-event index nil negative-expectation
      add multiply negate inverse zero one less)
     (ht059-scalar-p carrier mean)
     (equal
      mean
      (ht059-sub
       add negate positive-expectation negative-expectation)))))

(defun-sk ht059-integrable-p
    (carrier measure level-event index
             add multiply negate inverse zero one less)
  (exists (mean)
    (ht059-has-expectation-p
     carrier measure level-event index mean
     add multiply negate inverse zero one less)))

;; Pointwise convergence and almost-sure convergence are direct epsilon-N
;; predicates. A measurable event of probability one supplies the AE witness.

(defun ht059-partial-sum
    (x-family count omega add zero)
  (declare (xargs :measure (nfix count)))
  (if (zp count)
      zero
    (let ((index (1- count)))
      (ht059-add
       add
       (ht059-partial-sum
        x-family index omega add zero)
       (ht059-apply2 x-family index omega)))))

(defun ht059-running-average
    (x-family count omega add multiply inverse zero one)
  (if (zp count)
      zero
    (ht059-div
     multiply inverse
     (ht059-partial-sum
      x-family count omega add zero)
     (ht059-real-nat add zero one count))))

(defun-sk ht059-pointwise-limit-tail-p
    (x-family omega mean
              add multiply negate inverse zero one less
              epsilon cutoff)
  (forall (count)
    (implies
     (and
      (natp count)
      (natp cutoff)
      (<= cutoff count))
     (ht059-less-p
      less
      (ht059-abs
       less negate zero
       (ht059-sub
        add negate
        (ht059-running-average
         x-family count omega
         add multiply inverse zero one)
        mean))
      epsilon))))

(defun-sk ht059-pointwise-limit-cutoff-exists-p
    (x-family omega mean
              add multiply negate inverse zero one less epsilon)
  (exists (cutoff)
    (and
     (natp cutoff)
     (ht059-pointwise-limit-tail-p
      x-family omega mean
      add multiply negate inverse zero one less
      epsilon cutoff))))

(defun-sk ht059-pointwise-converges-p
    (carrier x-family omega mean
             add multiply negate inverse zero one less)
  (forall (epsilon)
    (implies
     (and
      (ht059-scalar-p carrier epsilon)
      (ht059-less-p less zero epsilon))
     (ht059-pointwise-limit-cutoff-exists-p
      x-family omega mean
      add multiply negate inverse zero one less epsilon))))

(defun-sk ht059-converges-on-event-p
    (carrier sample-carrier event-member good-event x-family mean
             add multiply negate inverse zero one less)
  (forall (omega)
    (implies
     (and
      (ht059-sample-p sample-carrier omega)
      (ht059-in-event-p event-member good-event omega))
     (ht059-pointwise-converges-p
      carrier x-family omega mean
      add multiply negate inverse zero one less))))

(defun-sk ht059-almost-sure-convergence-p
    (carrier one sample-carrier events event-member measure
             x-family mean add multiply negate inverse zero less)
  (exists (good-event)
    (and
     (ht059-event-p events good-event)
     (equal (ht059-apply1 measure good-event) one)
     (ht059-converges-on-event-p
      carrier sample-carrier event-member good-event x-family mean
      add multiply negate inverse zero one less))))

(defun ht059-random-variable-family-p
    (carrier zero negate less
             sample-carrier events event-member
             x-family ray-event level-event)
  (and
   (tamep-functionp x-family)
   (tamep-functionp ray-event)
   (tamep-functionp level-event)
   (ht059-family-values-p
    carrier sample-carrier x-family)
   (ht059-ray-event-closure-p
    carrier events ray-event)
   (ht059-ray-event-membership-p
    carrier sample-carrier event-member x-family ray-event less)
   (ht059-level-event-closure-p
    carrier zero less events level-event)
   (ht059-level-event-membership-p
    carrier sample-carrier event-member x-family level-event
    zero negate less)))

(defun ht059-strong-law-context-p
    (carrier zero one add multiply negate inverse less
             sample-carrier events event-member
             empty-event full-event complement-event intersection-event
             sequence-value countable-union-event measure
             x-family ray-event level-event)
  (and
   (ht059-real-field-p
    carrier zero one add multiply negate inverse less)
   (ht059-probability-space-p
    carrier zero one add negate less
    sample-carrier events event-member
    empty-event full-event complement-event intersection-event
    sequence-value countable-union-event measure)
   (ht059-random-variable-family-p
    carrier zero negate less
    sample-carrier events event-member
    x-family ray-event level-event)
   (ht059-identically-distributed-p
    carrier events measure ray-event)
   (ht059-pairwise-independent-p
    carrier events intersection-event measure ray-event multiply)
   (ht059-integrable-p
    carrier measure level-event 0
    add multiply negate inverse zero one less)))

(defun-sk ht059-strong-law-conclusion-p
    (carrier zero one add multiply negate inverse less
             sample-carrier events event-member measure
             x-family level-event)
  (exists (mean)
    (and
     (ht059-has-expectation-p
      carrier measure level-event 0 mean
      add multiply negate inverse zero one less)
     (ht059-almost-sure-convergence-p
      carrier one sample-carrier events event-member measure
      x-family mean add multiply negate inverse zero less))))

(defun hundred-theorems-059-laws-of-large-numbers-statement
    (carrier zero one add multiply negate inverse less
             sample-carrier events event-member
             empty-event full-event complement-event intersection-event
             sequence-value countable-union-event measure
             x-family ray-event level-event)
  (implies
   (ht059-strong-law-context-p
    carrier zero one add multiply negate inverse less
    sample-carrier events event-member
    empty-event full-event complement-event intersection-event
    sequence-value countable-union-event measure
    x-family ray-event level-event)
   (ht059-strong-law-conclusion-p
    carrier zero one add multiply negate inverse less
    sample-carrier events event-member measure
    x-family level-event)))

(value-triple :itpeval-statement-checked)
:q
