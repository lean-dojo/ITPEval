;; Statement-only formalization of NTP4VC corpus artifact
;; pearl/multiprecision/base_info_BaseInfo_wmpn_get_base_infoqtvc:
;; the verification condition for computing the largest successive power of a
;; base from 2 through 256 that fits in a 64-bit limb. This file contains no
;; proof.

(in-package "ACL2")

(set-inhibit-output-lst '(prove proof-tree event summary))

;; Natural numbers below 2^n are in bijection with the source unsigned
;; fixed-width words. Under this representation, unsigned conversion and word
;; equality are ordinary integer identity.

(defun get-base-info-bv32-p (value)
  (and
   (integerp value)
   (<= 0 value)
   (< value 4294967296)))

(defun get-base-info-bv64-p (value)
  (and
   (integerp value)
   (<= 0 value)
   (< value 18446744073709551616)))

;; The source record is extensional in these three fields and every value
;; satisfies the displayed invariant. Proper three-element lists therefore
;; give an exact concrete representation of the record type.

(defun get-base-info-record-p (result)
  (and
   (true-listp result)
   (equal (len result) 3)
   (integerp (car result))
   (get-base-info-bv32-p (cadr result))
   (get-base-info-bv64-p (caddr result))
   (<= 2 (car result))
   (<= (car result) 256)
   (< (caddr result) 18446744073709551616)
   (<= 18446744073709551616
       (* (caddr result) (car result)))
   (<= 7 (cadr result))
   (<= (cadr result) 63)
   (equal (caddr result)
          (expt (car result) (cadr result)))))

;; Preserve the universal continuation for the newly constructed source
;; record. The separate input-base and record-base arguments retain the scope
;; of the source branch-local integer binding.

(defun-sk get-base-info-result-continuation-p
    (input-base record-base exponent power)
  (forall (result)
    (implies
     (get-base-info-record-p result)
     (implies
      (and
       (equal (car result) record-base)
       (equal (cadr result) exponent)
       (equal (caddr result) power))
      (equal (car result) input-base)))))

;; After a successful multiplication, every 32-bit word equal to the
;; incremented exponent must establish the loop variant decrease and preserve
;; both loop invariants.

(defun-sk get-base-info-next-exponent-continuation-p
    (base quotient exponent power next-power)
  (forall (next-exponent)
    (implies
     (get-base-info-bv32-p next-exponent)
     (implies
      (equal next-exponent (+ exponent 1))
      (and
       (<= 0 (- quotient power))
       (< (- quotient next-power)
          (- quotient power))
       (equal (expt base next-exponent)
              next-power)
       (<= 1 next-exponent)
       (<= next-exponent 64))))))

;; The product and increment range checks remain outside their corresponding
;; universal continuations, as in the generated verification condition.

(defun-sk get-base-info-next-power-continuation-p
    (base quotient exponent power)
  (forall (next-power)
    (implies
     (get-base-info-bv64-p next-power)
     (implies
      (equal next-power (* power base))
      (and
       (get-base-info-bv32-p (+ exponent 1))
       (get-base-info-next-exponent-continuation-p
        base quotient exponent power next-power))))))

;; This is the loop-body/loop-exit split for every source-typed exponent and
;; power satisfying the loop invariants.

(defun-sk get-base-info-loop-continuation-p (base quotient)
  (forall (exponent power)
    (implies
     (and
      (get-base-info-bv32-p exponent)
      (get-base-info-bv64-p power))
     (implies
      (and
       (equal (expt base exponent) power)
       (<= 1 exponent)
       (<= exponent 64))
      (if (<= power quotient)
          (and
           (get-base-info-bv64-p (* power base))
           (get-base-info-next-power-continuation-p
            base quotient exponent power))
        (and
         (<= 2 base)
         (<= base 256)
         (< power 18446744073709551616)
         (<= 18446744073709551616
             (* power base))
         (<= 7 exponent)
         (<= exponent 63)
         (equal power (expt base exponent))
         (get-base-info-result-continuation-p
          base base exponent power)))))))

;; The original Why3 computation binds quotient to
;; floor((2^64 - 1) / base). Since the assumed base is positive, ACL2 floor
;; agrees with Why3 computer division here.

(defun-sk get-base-info-quotient-continuation-p (base)
  (forall (quotient)
    (implies
     (get-base-info-bv64-p quotient)
     (implies
      (equal quotient
             (floor 18446744073709551615 base))
      (and
       (equal (expt base 1) base)
       (<= 1 1)
       (<= 1 64)
       (get-base-info-loop-continuation-p
        base quotient))))))

(defun
    ntp4vc-pearl-multiprecision-base-info-baseinfo-wmpn-get-base-infoqtvc-statement
    (base)
  (implies
   (and
    (get-base-info-bv64-p base)
    (<= 2 base)
    (<= base 256))
   (and
    (not (equal base 0))
    (get-base-info-bv64-p
     (floor 18446744073709551615 base))
    (get-base-info-quotient-continuation-p base))))

(set-inhibit-output-lst nil)
(value-triple :itpeval-statement-checked)
:q
