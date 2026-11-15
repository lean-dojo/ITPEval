;; Statement-only formalization of NTP4VC corpus artifact
;; pearl/multiprecision/base_info_BaseInfo_wmpn_base_power_of_two_pqtvc:
;; the verification condition for recognizing powers of two from 2 through
;; 256 and returning their exponents in a 32-bit word. This file contains no
;; proof.

(in-package "ACL2")

(set-inhibit-output-lst '(prove proof-tree event summary))

;; Natural numbers below 2^n are in bijection with the source unsigned
;; fixed-width words.  Under this representation, unsigned conversion and
;; equality are ordinary integer identity.

(defun base-info-bv32-p (value)
  (and
   (integerp value)
   (<= 0 value)
   (< value 4294967296)))

(defun base-info-bv64-p (value)
  (and
   (integerp value)
   (<= 0 value)
   (< value 18446744073709551616)))

;; Each helper preserves one branch-local Boolean existential from the source
;; verification condition.  Later witnesses occur only in the corresponding
;; false branch, exactly matching their original quantifier scopes.

(defun-sk base-info-power-case-8-p (b result)
  (exists (o8)
    (and
     (booleanp o8)
     (implies
      (equal b 256)
      (equal o8 t))
     (implies
      (equal o8 t)
      (equal b 256))
     (if (equal o8 t)
         (equal result 8)
       (equal result 0)))))

(defun-sk base-info-power-case-7-p (b result)
  (exists (o7)
    (and
     (booleanp o7)
     (implies
      (equal b 128)
      (equal o7 t))
     (implies
      (equal o7 t)
      (equal b 128))
     (if (equal o7 t)
         (equal result 7)
       (base-info-power-case-8-p b result)))))

(defun-sk base-info-power-case-6-p (b result)
  (exists (o6)
    (and
     (booleanp o6)
     (implies
      (equal b 64)
      (equal o6 t))
     (implies
      (equal o6 t)
      (equal b 64))
     (if (equal o6 t)
         (equal result 6)
       (base-info-power-case-7-p b result)))))

(defun-sk base-info-power-case-5-p (b result)
  (exists (o5)
    (and
     (booleanp o5)
     (implies
      (equal b 32)
      (equal o5 t))
     (implies
      (equal o5 t)
      (equal b 32))
     (if (equal o5 t)
         (equal result 5)
       (base-info-power-case-6-p b result)))))

(defun-sk base-info-power-case-4-p (b result)
  (exists (o4)
    (and
     (booleanp o4)
     (implies
      (equal b 16)
      (equal o4 t))
     (implies
      (equal o4 t)
      (equal b 16))
     (if (equal o4 t)
         (equal result 4)
       (base-info-power-case-5-p b result)))))

(defun-sk base-info-power-case-3-p (b result)
  (exists (o3)
    (and
     (booleanp o3)
     (implies
      (equal b 8)
      (equal o3 t))
     (implies
      (equal o3 t)
      (equal b 8))
     (if (equal o3 t)
         (equal result 3)
       (base-info-power-case-4-p b result)))))

(defun-sk base-info-power-case-2-p (b result)
  (exists (o2)
    (and
     (booleanp o2)
     (implies
      (equal b 4)
      (equal o2 t))
     (implies
      (equal o2 t)
      (equal b 4))
     (if (equal o2 t)
         (equal result 2)
       (base-info-power-case-3-p b result)))))

(defun base-info-result-branch-p (b o1 result)
  (if (equal o1 t)
      (equal result 1)
    (base-info-power-case-2-p b result)))

;; The zero result excludes every power 2^n with an arbitrary nonnegative
;; mathematical-integer exponent.

(defun-sk base-info-no-nonnegative-power-p (b)
  (forall (n)
    (implies
     (integerp n)
     (implies
      (<= 0 n)
      (not
       (equal (expt 2 n) b))))))

(defun
    ntp4vc-pearl-multiprecision-base-info-baseinfo-wmpn-base-power-of-two-pqtvc-statement
    (b o1 result)
  (implies
   (and
    (base-info-bv64-p b)
    (booleanp o1)
    (base-info-bv32-p result)
    (<= 2 b)
    (<= b 256)
    (implies
     (equal b 2)
     (equal o1 t))
    (implies
     (equal o1 t)
     (equal b 2))
    (base-info-result-branch-p b o1 result))
   (and
    (<= 0 result)
    (<= result 8)
    (implies
     (not (equal result 0))
     (equal (expt 2 result) b))
    (implies
     (equal result 0)
     (base-info-no-nonnegative-power-p b)))))

(set-inhibit-output-lst nil)
(value-triple :itpeval-statement-checked)
:q
