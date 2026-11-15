;; Statement-only formalization of NTP4VC corpus artifact
;; frama_c/verker/sysfs_streq_Why3_ide_VCsysfs_streq_loop_inv_4_preserved_goal5:
;; preservation of the unsigned successor-index bound by the first string's
;; logical length, under the stated equal-character, memory, valid-string,
;; comparison, region, linkedness, constancy, and loop-prefix hypotheses.
;; This file contains no proof.

(in-package "ACL2")

(set-inhibit-output-lst '(prove proof-tree event summary))

;; Source addresses are exactly pairs of mathematical integers.

(defun sslip4g5-address-p (address)
  (and
   (consp address)
   (integerp (car address))
   (integerp (cdr address))))

(defun sslip4g5-address-base (address)
  (car address))

(defun sslip4g5-address-offset (address)
  (cdr address))

(defun sslip4g5-shift (address amount)
  (cons
   (sslip4g5-address-base address)
   (+ (sslip4g5-address-offset address)
      amount)))

;; Conservative interfaces represent the universally arbitrary character
;; memory t_1 and allocation map t, together with the source region, logical
;; strlen, logical strncmp, C integer conversions, linkedness, and constancy
;; symbols.

(defstub sslip4g5-character-memory (address) t)
(defstub sslip4g5-allocation (index) t)
(defstub sslip4g5-region (base) t)
(defstub sslip4g5-l-strlen (address) t)
(defstub sslip4g5-l-strncmp (left right count) t)
(defstub sslip4g5-to-uint64 (value) t)
(defstub sslip4g5-to-sint32 (value) t)
(defstub sslip4g5-linked-op () t)
(defstub sslip4g5-sconst-op () t)

;; Preserve the source function types over the full address and unbounded
;; mathematical-integer domains.

(defun-sk sslip4g5-function-types-p ()
  (forall (address index base value left right count)
    (and
     (implies
      (sslip4g5-address-p address)
      (and
       (integerp
        (sslip4g5-character-memory address))
       (integerp
        (sslip4g5-l-strlen address))))
     (implies
      (integerp index)
      (integerp
       (sslip4g5-allocation index)))
     (implies
      (integerp base)
      (integerp
       (sslip4g5-region base)))
     (implies
      (integerp value)
      (and
       (integerp
        (sslip4g5-to-uint64 value))
       (integerp
        (sslip4g5-to-sint32 value))))
     (implies
      (and
       (sslip4g5-address-p left)
       (sslip4g5-address-p right)
       (integerp count))
      (integerp
       (sslip4g5-l-strncmp left right count))))))

(defun sslip4g5-linked-p ()
  (if (sslip4g5-linked-op) t nil))

(defun sslip4g5-sconst-p ()
  (if (sslip4g5-sconst-op) t nil))

;; Exact mathematical ranges for the source C integer predicates.

(defun sslip4g5-is-sint8-p (value)
  (and
   (integerp value)
   (<= -128 value)
   (< value 128)))

(defun sslip4g5-is-sint32-p (value)
  (and
   (integerp value)
   (<= -2147483648 value)
   (< value 2147483648)))

(defun sslip4g5-is-uint64-p (value)
  (and
   (integerp value)
   (<= 0 value)
   (< value 18446744073709551616)))

;; Universal range, identity-on-range, and projection laws for the source C
;; integer conversions used by logical strlen and logical strncmp.

(defun-sk sslip4g5-to-uint64-laws-p ()
  (forall (value)
    (implies
     (integerp value)
     (and
      (sslip4g5-is-uint64-p
       (sslip4g5-to-uint64 value))
      (implies
       (sslip4g5-is-uint64-p value)
       (equal
        (sslip4g5-to-uint64 value)
        value))
      (equal
       (sslip4g5-to-uint64
        (sslip4g5-to-uint64 value))
       (sslip4g5-to-uint64 value))))))

(defun-sk sslip4g5-to-sint32-laws-p ()
  (forall (value)
    (implies
     (integerp value)
     (and
      (sslip4g5-is-sint32-p
       (sslip4g5-to-sint32 value))
      (implies
       (sslip4g5-is-sint32-p value)
       (equal
        (sslip4g5-to-sint32 value)
        value))
      (equal
       (sslip4g5-to-sint32
        (sslip4g5-to-sint32 value))
       (sslip4g5-to-sint32 value))))))

;; Exact unfolding of Memory.valid_rw for the arbitrary allocation map t.

(defun sslip4g5-valid-rw-p (address length)
  (implies
   (< 0 length)
   (and
    (< 0
       (sslip4g5-address-base address))
    (<= 0
        (sslip4g5-address-offset address))
    (<=
     (+ (sslip4g5-address-offset address)
        length)
     (sslip4g5-allocation
      (sslip4g5-address-base address))))))

;; Exact unfolding of A_Strlen.p_valid_str. Its null terminator remains an
;; internal existential over all mathematical integers, and its character
;; range condition remains universally quantified over all integers.

(defun-sk sslip4g5-string-chars-sint8-through-p
    (address bound)
  (forall (position)
    (implies
     (integerp position)
     (implies
      (<= position bound)
      (sslip4g5-is-sint8-p
       (sslip4g5-character-memory
        (sslip4g5-shift address position)))))))

(defun-sk sslip4g5-valid-string-p (address)
  (exists (index)
    (and
     (integerp index)
     (equal
      (sslip4g5-character-memory
       (sslip4g5-shift address index))
      0)
     (sslip4g5-is-uint64-p index)
     (sslip4g5-valid-rw-p
      (sslip4g5-shift address 0)
      (+ 1 index))
     (sslip4g5-string-chars-sint8-through-p
      address index))))

;; Universal closures of A_Strlen.fix_l_strlen and Q_TL_strlen.

(defun-sk sslip4g5-strlen-laws-p ()
  (forall (address)
    (implies
     (sslip4g5-address-p address)
     (and
      (if
          (equal
           (sslip4g5-character-memory
            (sslip4g5-shift address 0))
           0)
          (equal
           (sslip4g5-l-strlen address)
           0)
        (equal
         (sslip4g5-to-uint64
          (+ 1
             (sslip4g5-l-strlen
              (sslip4g5-shift address 1))))
         (sslip4g5-l-strlen address)))
      (sslip4g5-is-uint64-p
       (sslip4g5-l-strlen address))))))

;; Universal closures of A_StrnCmp.fix_l_strncmp_2' and Q_TL_strncmp_2'.

(defun-sk sslip4g5-strncmp-laws-p ()
  (forall (left right count)
    (implies
     (and
      (sslip4g5-address-p left)
      (sslip4g5-address-p right)
      (integerp count))
     (and
      (if
          (equal count 0)
          (equal
           (sslip4g5-l-strncmp left right count)
           0)
        (if
            (equal
             (sslip4g5-character-memory
              (sslip4g5-shift right 0))
             (sslip4g5-character-memory
              (sslip4g5-shift left 0)))
            (if
                (equal
                 (sslip4g5-character-memory
                  (sslip4g5-shift left 0))
                 0)
                (equal
                 (sslip4g5-l-strncmp left right count)
                 0)
              (equal
               (sslip4g5-l-strncmp
                (sslip4g5-shift left 1)
                (sslip4g5-shift right 1)
                (sslip4g5-to-uint64 (- count 1)))
               (sslip4g5-l-strncmp left right count)))
          (equal
           (sslip4g5-to-sint32
            (-
             (sslip4g5-character-memory
              (sslip4g5-shift left 0))
             (sslip4g5-character-memory
              (sslip4g5-shift right 0))))
           (sslip4g5-l-strncmp left right count))))
      (sslip4g5-is-sint32-p
       (sslip4g5-l-strncmp left right count))))))

(defun sslip4g5-strnequal-p (left right count)
  (equal
   (sslip4g5-l-strncmp left right count)
   0))

;; The source prefix hypothesis retains its universal quantifier over every
;; mathematical integer and its original nonnegative and strict upper bounds.

(defun-sk sslip4g5-prefix-equal-before-p
    (left right bound)
  (forall (position)
    (implies
     (integerp position)
     (implies
      (<= 0 position)
      (implies
       (< position bound)
       (equal
        (sslip4g5-character-memory
         (sslip4g5-shift left position))
        (sslip4g5-character-memory
         (sslip4g5-shift right position))))))))

(defun-sk
    ntp4vc-sysfs-streq-loop-inv-4-preserved-goal5-statement ()
  (forall
   (a1 i a)
   (implies
    (and
     (sslip4g5-address-p a1)
     (integerp i)
     (sslip4g5-address-p a)
     (sslip4g5-function-types-p)
     (sslip4g5-to-uint64-laws-p)
     (sslip4g5-to-sint32-laws-p)
     (sslip4g5-strlen-laws-p)
     (sslip4g5-strncmp-laws-p))
    (let*
        ((a2
          (sslip4g5-shift a1 i))
         (x
          (sslip4g5-character-memory a2))
         (a3
          (sslip4g5-shift a i))
         (x1
          (sslip4g5-character-memory a3))
         (x2
          (sslip4g5-l-strlen a1)))
      (implies
       (and
        (not (equal x 0))
        (equal x x1)
        (<= i
            (sslip4g5-l-strlen a))
        (<= i x2)
        (<=
         (sslip4g5-region
          (sslip4g5-address-base a))
         0)
        (<=
         (sslip4g5-region
          (sslip4g5-address-base a1))
         0)
        (sslip4g5-linked-p)
        (sslip4g5-sconst-p)
        (sslip4g5-is-uint64-p i)
        (sslip4g5-valid-string-p a)
        (sslip4g5-valid-string-p a1)
        (sslip4g5-strnequal-p a1 a i)
        (sslip4g5-is-sint8-p x1)
        (sslip4g5-is-sint8-p x)
        (sslip4g5-valid-string-p a3)
        (sslip4g5-valid-string-p a2)
        (sslip4g5-prefix-equal-before-p
         a1 a i))
       (<=
        (sslip4g5-to-uint64 (+ 1 i))
        x2))))))

(value-triple :itpeval-statement-checked)

:q
