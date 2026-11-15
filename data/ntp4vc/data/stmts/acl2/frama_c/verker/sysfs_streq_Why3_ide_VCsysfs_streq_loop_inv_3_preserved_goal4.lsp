;; Statement-only formalization of NTP4VC corpus artifact
;; frama_c/verker/sysfs_streq_Why3_ide_VCsysfs_streq_loop_inv_3_preserved_goal4:
;; preservation of validity for both strings after advancing their shared
;; nonzero equal-character prefix index, under the stated memory, string,
;; comparison, region, linkedness, constancy, and loop-prefix hypotheses.
;; This file contains no proof.

(in-package "ACL2")

(set-inhibit-output-lst '(prove proof-tree event summary))

;; Source addresses are exactly pairs of mathematical integers.

(defun sslip3g4-address-p (address)
  (and
   (consp address)
   (integerp (car address))
   (integerp (cdr address))))

(defun sslip3g4-address-base (address)
  (car address))

(defun sslip3g4-address-offset (address)
  (cdr address))

(defun sslip3g4-shift (address amount)
  (cons
   (sslip3g4-address-base address)
   (+ (sslip3g4-address-offset address)
      amount)))

;; Conservative interfaces represent the universally arbitrary character
;; memory t_1 and allocation map t, together with the source region, logical
;; strlen, logical strncmp, C integer conversions, linkedness, and constancy
;; symbols.

(defstub sslip3g4-character-memory (address) t)
(defstub sslip3g4-allocation (index) t)
(defstub sslip3g4-region (base) t)
(defstub sslip3g4-l-strlen (address) t)
(defstub sslip3g4-l-strncmp (left right count) t)
(defstub sslip3g4-to-uint64 (value) t)
(defstub sslip3g4-to-sint32 (value) t)
(defstub sslip3g4-linked-op () t)
(defstub sslip3g4-sconst-op () t)

;; Preserve the source function types over the full address and unbounded
;; mathematical-integer domains.

(defun-sk sslip3g4-function-types-p ()
  (forall (address index base value left right count)
    (and
     (implies
      (sslip3g4-address-p address)
      (and
       (integerp
        (sslip3g4-character-memory address))
       (integerp
        (sslip3g4-l-strlen address))))
     (implies
      (integerp index)
      (integerp
       (sslip3g4-allocation index)))
     (implies
      (integerp base)
      (integerp
       (sslip3g4-region base)))
     (implies
      (integerp value)
      (and
       (integerp
        (sslip3g4-to-uint64 value))
       (integerp
        (sslip3g4-to-sint32 value))))
     (implies
      (and
       (sslip3g4-address-p left)
       (sslip3g4-address-p right)
       (integerp count))
      (integerp
       (sslip3g4-l-strncmp left right count))))))

(defun sslip3g4-linked-p ()
  (if (sslip3g4-linked-op) t nil))

(defun sslip3g4-sconst-p ()
  (if (sslip3g4-sconst-op) t nil))

;; Exact mathematical ranges for the source C integer predicates.

(defun sslip3g4-is-sint8-p (value)
  (and
   (integerp value)
   (<= -128 value)
   (< value 128)))

(defun sslip3g4-is-sint32-p (value)
  (and
   (integerp value)
   (<= -2147483648 value)
   (< value 2147483648)))

(defun sslip3g4-is-uint64-p (value)
  (and
   (integerp value)
   (<= 0 value)
   (< value 18446744073709551616)))

;; Universal range, identity-on-range, and projection laws for the source C
;; integer conversions used by logical strlen and logical strncmp.

(defun-sk sslip3g4-to-uint64-laws-p ()
  (forall (value)
    (implies
     (integerp value)
     (and
      (sslip3g4-is-uint64-p
       (sslip3g4-to-uint64 value))
      (implies
       (sslip3g4-is-uint64-p value)
       (equal
        (sslip3g4-to-uint64 value)
        value))
      (equal
       (sslip3g4-to-uint64
        (sslip3g4-to-uint64 value))
       (sslip3g4-to-uint64 value))))))

(defun-sk sslip3g4-to-sint32-laws-p ()
  (forall (value)
    (implies
     (integerp value)
     (and
      (sslip3g4-is-sint32-p
       (sslip3g4-to-sint32 value))
      (implies
       (sslip3g4-is-sint32-p value)
       (equal
        (sslip3g4-to-sint32 value)
        value))
      (equal
       (sslip3g4-to-sint32
        (sslip3g4-to-sint32 value))
       (sslip3g4-to-sint32 value))))))

;; Exact unfolding of Memory.valid_rw for the arbitrary allocation map t.

(defun sslip3g4-valid-rw-p (address length)
  (implies
   (< 0 length)
   (and
    (< 0
       (sslip3g4-address-base address))
    (<= 0
        (sslip3g4-address-offset address))
    (<=
     (+ (sslip3g4-address-offset address)
        length)
     (sslip3g4-allocation
      (sslip3g4-address-base address))))))

;; Exact unfolding of A_Strlen.p_valid_str. Its null terminator remains an
;; internal existential over all mathematical integers, and its character
;; range condition remains universally quantified over all integers.

(defun-sk sslip3g4-string-chars-sint8-through-p
    (address bound)
  (forall (position)
    (implies
     (integerp position)
     (implies
      (<= position bound)
      (sslip3g4-is-sint8-p
       (sslip3g4-character-memory
        (sslip3g4-shift address position)))))))

(defun-sk sslip3g4-valid-string-p (address)
  (exists (index)
    (and
     (integerp index)
     (equal
      (sslip3g4-character-memory
       (sslip3g4-shift address index))
      0)
     (sslip3g4-is-uint64-p index)
     (sslip3g4-valid-rw-p
      (sslip3g4-shift address 0)
      (+ 1 index))
     (sslip3g4-string-chars-sint8-through-p
      address index))))

;; Universal closures of A_Strlen.fix_l_strlen and Q_TL_strlen.

(defun-sk sslip3g4-strlen-laws-p ()
  (forall (address)
    (implies
     (sslip3g4-address-p address)
     (and
      (if
          (equal
           (sslip3g4-character-memory
            (sslip3g4-shift address 0))
           0)
          (equal
           (sslip3g4-l-strlen address)
           0)
        (equal
         (sslip3g4-to-uint64
          (+ 1
             (sslip3g4-l-strlen
              (sslip3g4-shift address 1))))
         (sslip3g4-l-strlen address)))
      (sslip3g4-is-uint64-p
       (sslip3g4-l-strlen address))))))

;; Universal closures of A_StrnCmp.fix_l_strncmp_2' and Q_TL_strncmp_2'.

(defun-sk sslip3g4-strncmp-laws-p ()
  (forall (left right count)
    (implies
     (and
      (sslip3g4-address-p left)
      (sslip3g4-address-p right)
      (integerp count))
     (and
      (if
          (equal count 0)
          (equal
           (sslip3g4-l-strncmp left right count)
           0)
        (if
            (equal
             (sslip3g4-character-memory
              (sslip3g4-shift right 0))
             (sslip3g4-character-memory
              (sslip3g4-shift left 0)))
            (if
                (equal
                 (sslip3g4-character-memory
                  (sslip3g4-shift left 0))
                 0)
                (equal
                 (sslip3g4-l-strncmp left right count)
                 0)
              (equal
               (sslip3g4-l-strncmp
                (sslip3g4-shift left 1)
                (sslip3g4-shift right 1)
                (sslip3g4-to-uint64 (- count 1)))
               (sslip3g4-l-strncmp left right count)))
          (equal
           (sslip3g4-to-sint32
            (-
             (sslip3g4-character-memory
              (sslip3g4-shift left 0))
             (sslip3g4-character-memory
              (sslip3g4-shift right 0))))
           (sslip3g4-l-strncmp left right count))))
      (sslip3g4-is-sint32-p
       (sslip3g4-l-strncmp left right count))))))

(defun sslip3g4-strnequal-p (left right count)
  (equal
   (sslip3g4-l-strncmp left right count)
   0))

;; The source prefix hypothesis retains its universal quantifier over every
;; mathematical integer and its original nonnegative and strict upper bounds.

(defun-sk sslip3g4-prefix-equal-before-p
    (left right bound)
  (forall (position)
    (implies
     (integerp position)
     (implies
      (<= 0 position)
      (implies
       (< position bound)
       (equal
        (sslip3g4-character-memory
         (sslip3g4-shift left position))
        (sslip3g4-character-memory
         (sslip3g4-shift right position))))))))

(defun-sk
    ntp4vc-sysfs-streq-loop-inv-3-preserved-goal4-statement ()
  (forall
   (a1 i a)
   (implies
    (and
     (sslip3g4-address-p a1)
     (integerp i)
     (sslip3g4-address-p a)
     (sslip3g4-function-types-p)
     (sslip3g4-to-uint64-laws-p)
     (sslip3g4-to-sint32-laws-p)
     (sslip3g4-strlen-laws-p)
     (sslip3g4-strncmp-laws-p))
    (let*
        ((a2
          (sslip3g4-shift a1 i))
         (x
          (sslip3g4-character-memory a2))
         (a3
          (sslip3g4-shift a i))
         (x1
          (sslip3g4-character-memory a3))
         (x2
          (+ 1 i)))
      (implies
       (and
        (not (equal x 0))
        (equal x x1)
        (<= i
            (sslip3g4-l-strlen a))
        (<= i
            (sslip3g4-l-strlen a1))
        (<=
         (sslip3g4-region
          (sslip3g4-address-base a))
         0)
        (<=
         (sslip3g4-region
          (sslip3g4-address-base a1))
         0)
        (sslip3g4-linked-p)
        (sslip3g4-sconst-p)
        (sslip3g4-is-uint64-p i)
        (sslip3g4-valid-string-p a)
        (sslip3g4-valid-string-p a1)
        (sslip3g4-strnequal-p a1 a i)
        (sslip3g4-is-sint8-p x1)
        (sslip3g4-is-sint8-p x)
        (sslip3g4-valid-string-p a3)
        (sslip3g4-valid-string-p a2)
        (sslip3g4-prefix-equal-before-p
         a1 a i))
       (and
        (sslip3g4-valid-string-p
         (sslip3g4-shift a x2))
        (sslip3g4-valid-string-p
         (sslip3g4-shift a1 x2))))))))

(value-triple :itpeval-statement-checked)

:q
