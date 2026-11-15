;; Statement-only formalization of NTP4VC corpus artifact
;; frama_c/verker/strlen_Why3_ide_VCstrlen_post_3_goal2:
;; the strlen postcondition that every nonnegative offset strictly before the
;; uint64-converted distance to the current null-byte address contains a
;; nonzero character, under the stated memory, length, region, linkedness,
;; constancy, address-order, valid-string, and signed-byte hypotheses. This
;; file contains no proof.

(in-package "ACL2")

(set-inhibit-output-lst '(prove proof-tree event summary))

;; Source addresses are exactly pairs of mathematical integers.

(defun sp3g2-address-p (address)
  (and
   (consp address)
   (integerp (car address))
   (integerp (cdr address))))

(defun sp3g2-address-base (address)
  (car address))

(defun sp3g2-address-offset (address)
  (cdr address))

(defun sp3g2-shift (address amount)
  (cons
   (sp3g2-address-base address)
   (+ (sp3g2-address-offset address) amount)))

;; Conservative interfaces represent the universally arbitrary character
;; memory t_1 and allocation map t, together with the source region,
;; address-order, logical strlen, unsigned conversion, linkedness, and
;; constancy symbols.

(defstub sp3g2-character-memory (address) t)
(defstub sp3g2-allocation (index) t)
(defstub sp3g2-region (base) t)
(defstub sp3g2-addr-le-op (left right) t)
(defstub sp3g2-l-strlen (address) t)
(defstub sp3g2-to-uint64 (value) t)
(defstub sp3g2-linked-op () t)
(defstub sp3g2-sconst-op () t)

;; Preserve the source function types over the full address and unbounded
;; mathematical-integer domains.

(defun-sk sp3g2-function-types-p ()
  (forall (address index base value)
    (and
     (implies
      (sp3g2-address-p address)
      (and
       (integerp
        (sp3g2-character-memory address))
       (integerp
        (sp3g2-l-strlen address))))
     (implies
      (integerp index)
      (integerp
       (sp3g2-allocation index)))
     (implies
      (integerp base)
      (integerp
       (sp3g2-region base)))
     (implies
      (integerp value)
      (integerp
       (sp3g2-to-uint64 value))))))

(defun sp3g2-addr-le-p (left right)
  (if (sp3g2-addr-le-op left right) t nil))

;; On addresses with equal bases, the source address relation is exactly
;; mathematical-integer order on offsets.

(defun-sk sp3g2-address-order-law-p ()
  (forall (left right)
    (implies
     (and
      (sp3g2-address-p left)
      (sp3g2-address-p right)
      (equal
       (sp3g2-address-base left)
       (sp3g2-address-base right)))
     (equal
      (sp3g2-addr-le-p left right)
      (<=
       (sp3g2-address-offset left)
       (sp3g2-address-offset right))))))

(defun sp3g2-linked-p ()
  (if (sp3g2-linked-op) t nil))

(defun sp3g2-sconst-p ()
  (if (sp3g2-sconst-op) t nil))

;; Exact mathematical ranges for the source C integer predicates.

(defun sp3g2-is-sint8-p (value)
  (and
   (integerp value)
   (<= -128 value)
   (< value 128)))

(defun sp3g2-is-uint64-p (value)
  (and
   (integerp value)
   (<= 0 value)
   (< value 18446744073709551616)))

;; Universal range, identity-on-range, and projection laws for the source's
;; abstract Cint.to_uint64 operation.

(defun-sk sp3g2-to-uint64-laws-p ()
  (forall (value)
    (implies
     (integerp value)
     (and
      (sp3g2-is-uint64-p
       (sp3g2-to-uint64 value))
      (implies
       (sp3g2-is-uint64-p value)
       (equal
        (sp3g2-to-uint64 value)
        value))
      (equal
       (sp3g2-to-uint64
        (sp3g2-to-uint64 value))
       (sp3g2-to-uint64 value))))))

;; Exact unfolding of Memory.valid_rw for the arbitrary allocation map t.

(defun sp3g2-valid-rw-p (address length)
  (implies
   (< 0 length)
   (and
    (< 0
       (sp3g2-address-base address))
    (<= 0
        (sp3g2-address-offset address))
    (<=
     (+ (sp3g2-address-offset address)
        length)
     (sp3g2-allocation
      (sp3g2-address-base address))))))

;; Exact unfolding of A_Strlen.p_valid_str. The terminating position remains
;; an internal existential over all mathematical integers, and its character
;; range condition remains universally quantified over all integers.

(defun-sk sp3g2-string-chars-sint8-through-p
    (address bound)
  (forall (position)
    (implies
     (integerp position)
     (implies
      (<= position bound)
      (sp3g2-is-sint8-p
       (sp3g2-character-memory
        (sp3g2-shift address position)))))))

(defun-sk sp3g2-valid-string-p (address)
  (exists (index)
    (and
     (integerp index)
     (equal
      (sp3g2-character-memory
       (sp3g2-shift address index))
      0)
     (sp3g2-is-uint64-p index)
     (sp3g2-valid-rw-p
      (sp3g2-shift address 0)
      (+ 1 index))
     (sp3g2-string-chars-sint8-through-p
      address index))))

;; Universal closures of A_Strlen.fix_l_strlen and Q_TL_strlen.

(defun-sk sp3g2-strlen-laws-p ()
  (forall (address)
    (implies
     (sp3g2-address-p address)
     (and
      (if
          (equal
           (sp3g2-character-memory
            (sp3g2-shift address 0))
           0)
          (equal
           (sp3g2-l-strlen address)
           0)
        (equal
         (sp3g2-to-uint64
          (+ 1
             (sp3g2-l-strlen
              (sp3g2-shift address 1))))
         (sp3g2-l-strlen address)))
      (sp3g2-is-uint64-p
       (sp3g2-l-strlen address))))))

(defun-sk ntp4vc-strlen-post-3-goal2-statement ()
  (forall
   (a1 a i)
   (implies
    (and
     (sp3g2-address-p a1)
     (sp3g2-address-p a)
     (integerp i)
     (sp3g2-function-types-p)
     (sp3g2-address-order-law-p)
     (sp3g2-to-uint64-laws-p)
     (sp3g2-strlen-laws-p))
    (let*
        ((x
          (sp3g2-address-offset a1))
         (x1
          (sp3g2-l-strlen a1))
         (x2
          (sp3g2-address-offset a))
         (x3
          (sp3g2-to-uint64
           (- x2 x))))
      (implies
       (and
        (equal
         (sp3g2-character-memory a)
         0)
        (equal
         (+ x x1)
         (+ x2
            (sp3g2-l-strlen a)))
        (<= 0 i)
        (<=
         (sp3g2-region
          (sp3g2-address-base a1))
         0)
        (< i x3)
        (sp3g2-linked-p)
        (sp3g2-sconst-p)
        (sp3g2-addr-le-p a1 a)
        (sp3g2-valid-string-p a)
        (sp3g2-valid-string-p a1)
        (sp3g2-addr-le-p
         a
         (sp3g2-shift a1 x1))
        (sp3g2-is-sint8-p
         (sp3g2-character-memory
          (sp3g2-shift a1 x3))))
       (not
        (equal
         (sp3g2-character-memory
          (sp3g2-shift a1 i))
         0)))))))

(value-triple :itpeval-statement-checked)

:q
