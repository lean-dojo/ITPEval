;; Statement-only formalization of NTP4VC corpus artifact
;; frama_c/verker/strlen_Why3_ide_VCstrlen_post_2_goal1:
;; the strlen postcondition that a character read at the uint64-converted
;; offset difference from the initial address is zero, under the stated
;; memory, length, region, linkedness, constancy, address-order, valid-string,
;; and signed-byte hypotheses. This file contains no proof.

(in-package "ACL2")

(set-inhibit-output-lst '(prove proof-tree event summary))

;; Source addresses are exactly pairs of mathematical integers.

(defun sp2g1-address-p (address)
  (and
   (consp address)
   (integerp (car address))
   (integerp (cdr address))))

(defun sp2g1-address-base (address)
  (car address))

(defun sp2g1-address-offset (address)
  (cdr address))

(defun sp2g1-shift (address amount)
  (cons
   (sp2g1-address-base address)
   (+ (sp2g1-address-offset address) amount)))

;; Conservative interfaces represent the universally arbitrary character
;; memory t_1 and allocation map t, together with the source region,
;; address-order, logical strlen, unsigned conversion, linkedness, and
;; constancy symbols.

(defstub sp2g1-character-memory (address) t)
(defstub sp2g1-allocation (index) t)
(defstub sp2g1-region (base) t)
(defstub sp2g1-addr-le-op (left right) t)
(defstub sp2g1-l-strlen (address) t)
(defstub sp2g1-to-uint64 (value) t)
(defstub sp2g1-linked-op () t)
(defstub sp2g1-sconst-op () t)

;; Preserve the source function types over the full address and unbounded
;; mathematical-integer domains.

(defun-sk sp2g1-function-types-p ()
  (forall (address index base value)
    (and
     (implies
      (sp2g1-address-p address)
      (and
       (integerp
        (sp2g1-character-memory address))
       (integerp
        (sp2g1-l-strlen address))))
     (implies
      (integerp index)
      (integerp
       (sp2g1-allocation index)))
     (implies
      (integerp base)
      (integerp
       (sp2g1-region base)))
     (implies
      (integerp value)
      (integerp
       (sp2g1-to-uint64 value))))))

(defun sp2g1-addr-le-p (left right)
  (if (sp2g1-addr-le-op left right) t nil))

;; On addresses with equal bases, the source address relation is exactly
;; mathematical-integer order on offsets.

(defun-sk sp2g1-address-order-law-p ()
  (forall (left right)
    (implies
     (and
      (sp2g1-address-p left)
      (sp2g1-address-p right)
      (equal
       (sp2g1-address-base left)
       (sp2g1-address-base right)))
     (equal
      (sp2g1-addr-le-p left right)
      (<=
       (sp2g1-address-offset left)
       (sp2g1-address-offset right))))))

(defun sp2g1-linked-p ()
  (if (sp2g1-linked-op) t nil))

(defun sp2g1-sconst-p ()
  (if (sp2g1-sconst-op) t nil))

;; Exact mathematical ranges for the source C integer predicates.

(defun sp2g1-is-sint8-p (value)
  (and
   (integerp value)
   (<= -128 value)
   (< value 128)))

(defun sp2g1-is-uint64-p (value)
  (and
   (integerp value)
   (<= 0 value)
   (< value 18446744073709551616)))

;; Universal range, identity-on-range, and projection laws for the source's
;; abstract Cint.to_uint64 operation.

(defun-sk sp2g1-to-uint64-laws-p ()
  (forall (value)
    (implies
     (integerp value)
     (and
      (sp2g1-is-uint64-p
       (sp2g1-to-uint64 value))
      (implies
       (sp2g1-is-uint64-p value)
       (equal
        (sp2g1-to-uint64 value)
        value))
      (equal
       (sp2g1-to-uint64
        (sp2g1-to-uint64 value))
       (sp2g1-to-uint64 value))))))

;; Exact unfolding of Memory.valid_rw for the arbitrary allocation map t.

(defun sp2g1-valid-rw-p (address length)
  (implies
   (< 0 length)
   (and
    (< 0
       (sp2g1-address-base address))
    (<= 0
        (sp2g1-address-offset address))
    (<=
     (+ (sp2g1-address-offset address)
        length)
     (sp2g1-allocation
      (sp2g1-address-base address))))))

;; Exact unfolding of A_Strlen.p_valid_str. The terminating position remains
;; an internal existential over all mathematical integers, and its character
;; range condition remains universally quantified over all integers.

(defun-sk sp2g1-string-chars-sint8-through-p
    (address bound)
  (forall (position)
    (implies
     (integerp position)
     (implies
      (<= position bound)
      (sp2g1-is-sint8-p
       (sp2g1-character-memory
        (sp2g1-shift address position)))))))

(defun-sk sp2g1-valid-string-p (address)
  (exists (index)
    (and
     (integerp index)
     (equal
      (sp2g1-character-memory
       (sp2g1-shift address index))
      0)
     (sp2g1-is-uint64-p index)
     (sp2g1-valid-rw-p
      (sp2g1-shift address 0)
      (+ 1 index))
     (sp2g1-string-chars-sint8-through-p
      address index))))

;; Universal closures of A_Strlen.fix_l_strlen and Q_TL_strlen.

(defun-sk sp2g1-strlen-laws-p ()
  (forall (address)
    (implies
     (sp2g1-address-p address)
     (and
      (if
          (equal
           (sp2g1-character-memory
            (sp2g1-shift address 0))
           0)
          (equal
           (sp2g1-l-strlen address)
           0)
        (equal
         (sp2g1-to-uint64
          (+ 1
             (sp2g1-l-strlen
              (sp2g1-shift address 1))))
         (sp2g1-l-strlen address)))
      (sp2g1-is-uint64-p
       (sp2g1-l-strlen address))))))

(defun-sk ntp4vc-strlen-post-2-goal1-statement ()
  (forall
   (a a1)
   (implies
    (and
     (sp2g1-address-p a)
     (sp2g1-address-p a1)
     (sp2g1-function-types-p)
     (sp2g1-address-order-law-p)
     (sp2g1-to-uint64-laws-p)
     (sp2g1-strlen-laws-p))
    (let*
        ((x
          (sp2g1-address-offset a1))
         (x1
          (sp2g1-l-strlen a1))
         (x2
          (sp2g1-address-offset a))
         (x3
          (sp2g1-character-memory
           (sp2g1-shift
            a1
            (sp2g1-to-uint64
             (- x2 x))))))
      (implies
       (and
        (equal
         (sp2g1-character-memory a)
         0)
        (equal
         (+ x x1)
         (+ x2
            (sp2g1-l-strlen a)))
        (<=
         (sp2g1-region
          (sp2g1-address-base a1))
         0)
        (sp2g1-linked-p)
        (sp2g1-sconst-p)
        (sp2g1-addr-le-p a1 a)
        (sp2g1-valid-string-p a)
        (sp2g1-valid-string-p a1)
        (sp2g1-addr-le-p
         a
         (sp2g1-shift a1 x1))
        (sp2g1-is-sint8-p x3))
       (equal x3 0))))))

(value-triple :itpeval-statement-checked)

:q
