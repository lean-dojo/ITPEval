;; Statement-only formalization of NTP4VC corpus artifact
;; frama_c/verker/strlen_Why3_ide_VCstrlen_loop_inv_2_preserved_goal5:
;; preservation of valid-string memory after advancing the current strlen
;; address by one, under the stated length-offset, region, linkedness,
;; constancy, address-order, character-range, and string-validity hypotheses.
;; This file contains no proof.

(in-package "ACL2")

(set-inhibit-output-lst '(prove proof-tree event summary))

;; Source addresses are exactly pairs of mathematical integers.

(defun slg5-address-p (address)
  (and
   (consp address)
   (integerp (car address))
   (integerp (cdr address))))

(defun slg5-address-base (address)
  (car address))

(defun slg5-address-offset (address)
  (cdr address))

(defun slg5-shift (address amount)
  (cons
   (slg5-address-base address)
   (+ (slg5-address-offset address) amount)))

;; Conservative interfaces represent the universally arbitrary character
;; memory t_1 and allocation map t, together with the source region,
;; address-order, logical strlen, unsigned conversion, linkedness, and
;; constancy symbols.

(defstub slg5-character-memory (address) t)
(defstub slg5-allocation (index) t)
(defstub slg5-region (base) t)
(defstub slg5-addr-le-op (left right) t)
(defstub slg5-l-strlen (address) t)
(defstub slg5-to-uint64 (value) t)
(defstub slg5-linked-op () t)
(defstub slg5-sconst-op () t)

;; Preserve the source function types over the full address and unbounded
;; mathematical-integer domains.

(defun-sk slg5-function-types-p ()
  (forall (address index base value)
    (and
     (implies
      (slg5-address-p address)
      (and
       (integerp
        (slg5-character-memory address))
       (integerp
        (slg5-l-strlen address))))
     (implies
      (integerp index)
      (integerp
       (slg5-allocation index)))
     (implies
      (integerp base)
      (integerp
       (slg5-region base)))
     (implies
      (integerp value)
      (integerp
       (slg5-to-uint64 value))))))

(defun slg5-addr-le-p (left right)
  (if (slg5-addr-le-op left right) t nil))

;; On addresses with equal bases, the source address relation is exactly
;; mathematical-integer order on offsets.

(defun-sk slg5-address-order-law-p ()
  (forall (left right)
    (implies
     (and
      (slg5-address-p left)
      (slg5-address-p right)
      (equal
       (slg5-address-base left)
       (slg5-address-base right)))
     (equal
      (slg5-addr-le-p left right)
      (<=
       (slg5-address-offset left)
       (slg5-address-offset right))))))

(defun slg5-linked-p ()
  (if (slg5-linked-op) t nil))

(defun slg5-sconst-p ()
  (if (slg5-sconst-op) t nil))

;; Exact mathematical ranges for the source C integer predicates.

(defun slg5-is-sint8-p (value)
  (and
   (integerp value)
   (<= -128 value)
   (< value 128)))

(defun slg5-is-uint64-p (value)
  (and
   (integerp value)
   (<= 0 value)
   (< value 18446744073709551616)))

;; Universal range, identity-on-range, and projection laws for the source's
;; abstract Cint.to_uint64 operation.

(defun-sk slg5-to-uint64-laws-p ()
  (forall (value)
    (implies
     (integerp value)
     (and
      (slg5-is-uint64-p
       (slg5-to-uint64 value))
      (implies
       (slg5-is-uint64-p value)
       (equal
        (slg5-to-uint64 value)
        value))
      (equal
       (slg5-to-uint64
        (slg5-to-uint64 value))
       (slg5-to-uint64 value))))))

;; Exact unfolding of Memory.valid_rw for the arbitrary allocation map t.

(defun slg5-valid-rw-p (address length)
  (implies
   (< 0 length)
   (and
    (< 0
       (slg5-address-base address))
    (<= 0
        (slg5-address-offset address))
    (<=
     (+ (slg5-address-offset address)
        length)
     (slg5-allocation
      (slg5-address-base address))))))

;; Exact unfolding of A_Strlen.p_valid_str. The terminating position remains
;; an internal existential over all mathematical integers, and its character
;; range condition remains universally quantified over all integers.

(defun-sk slg5-string-chars-sint8-through-p
    (address bound)
  (forall (position)
    (implies
     (integerp position)
     (implies
      (<= position bound)
      (slg5-is-sint8-p
       (slg5-character-memory
        (slg5-shift address position)))))))

(defun-sk slg5-valid-string-p (address)
  (exists (index)
    (and
     (integerp index)
     (equal
      (slg5-character-memory
       (slg5-shift address index))
      0)
     (slg5-is-uint64-p index)
     (slg5-valid-rw-p
      (slg5-shift address 0)
      (+ 1 index))
     (slg5-string-chars-sint8-through-p
      address index))))

;; Universal closures of A_Strlen.fix_l_strlen and Q_TL_strlen.

(defun-sk slg5-strlen-laws-p ()
  (forall (address)
    (implies
     (slg5-address-p address)
     (and
      (if
          (equal
           (slg5-character-memory
            (slg5-shift address 0))
           0)
          (equal
           (slg5-l-strlen address)
           0)
        (equal
         (slg5-to-uint64
          (+ 1
             (slg5-l-strlen
              (slg5-shift address 1))))
         (slg5-l-strlen address)))
      (slg5-is-uint64-p
       (slg5-l-strlen address))))))

(defun-sk
    ntp4vc-strlen-loop-inv-2-preserved-goal5-statement ()
  (forall
   (a a1)
   (implies
    (and
     (slg5-address-p a)
     (slg5-address-p a1)
     (slg5-function-types-p)
     (slg5-address-order-law-p)
     (slg5-to-uint64-laws-p)
     (slg5-strlen-laws-p))
    (let*
        ((x
          (slg5-character-memory a))
         (x1
          (slg5-l-strlen a1)))
      (implies
       (and
        (not (equal x 0))
        (equal
         (+ (slg5-address-offset a1)
            x1)
         (+ (slg5-address-offset a)
            (slg5-l-strlen a)))
        (<=
         (slg5-region
          (slg5-address-base a1))
         0)
        (slg5-linked-p)
        (slg5-sconst-p)
        (slg5-addr-le-p a1 a)
        (slg5-is-sint8-p x)
        (slg5-valid-string-p a)
        (slg5-valid-string-p a1)
        (slg5-addr-le-p
         a
         (slg5-shift a1 x1)))
       (slg5-valid-string-p
        (slg5-shift a 1)))))))

(value-triple :itpeval-statement-checked)

:q
