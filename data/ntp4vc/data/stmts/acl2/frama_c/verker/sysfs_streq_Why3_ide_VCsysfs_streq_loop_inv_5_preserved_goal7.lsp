;; Statement-only formalization of NTP4VC corpus artifact
;; frama_c/verker/sysfs_streq_Why3_ide_VCsysfs_streq_loop_inv_5_preserved_goal7:
;; preservation of the unsigned successor-index bound by the second string's
;; logical length, under the stated equal-character, memory, valid-string,
;; comparison, region, linkedness, constancy, and loop-prefix hypotheses.
;; This file contains no proof.

(in-package "ACL2")

(set-inhibit-output-lst '(prove proof-tree event summary))

;; Source addresses are exactly pairs of mathematical integers.

(defun sslip5g7-address-p (address)
  (and
   (consp address)
   (integerp (car address))
   (integerp (cdr address))))

(defun sslip5g7-address-base (address)
  (car address))

(defun sslip5g7-address-offset (address)
  (cdr address))

(defun sslip5g7-shift (address amount)
  (cons
   (sslip5g7-address-base address)
   (+ (sslip5g7-address-offset address)
      amount)))

;; Conservative interfaces represent the universally arbitrary character
;; memory t_1 and allocation map t, together with the source region, logical
;; strlen, logical strncmp, C integer conversions, linkedness, and constancy
;; symbols.

(defstub sslip5g7-character-memory (address) t)
(defstub sslip5g7-allocation (index) t)
(defstub sslip5g7-region (base) t)
(defstub sslip5g7-l-strlen (address) t)
(defstub sslip5g7-l-strncmp (left right count) t)
(defstub sslip5g7-to-uint64 (value) t)
(defstub sslip5g7-to-sint32 (value) t)
(defstub sslip5g7-linked-op () t)
(defstub sslip5g7-sconst-op () t)

;; Preserve the source function types over the full address and unbounded
;; mathematical-integer domains.

(defun-sk sslip5g7-function-types-p ()
  (forall (address index base value left right count)
    (and
     (implies
      (sslip5g7-address-p address)
      (and
       (integerp
        (sslip5g7-character-memory address))
       (integerp
        (sslip5g7-l-strlen address))))
     (implies
      (integerp index)
      (integerp
       (sslip5g7-allocation index)))
     (implies
      (integerp base)
      (integerp
       (sslip5g7-region base)))
     (implies
      (integerp value)
      (and
       (integerp
        (sslip5g7-to-uint64 value))
       (integerp
        (sslip5g7-to-sint32 value))))
     (implies
      (and
       (sslip5g7-address-p left)
       (sslip5g7-address-p right)
       (integerp count))
      (integerp
       (sslip5g7-l-strncmp left right count))))))

(defun sslip5g7-linked-p ()
  (if (sslip5g7-linked-op) t nil))

(defun sslip5g7-sconst-p ()
  (if (sslip5g7-sconst-op) t nil))

;; Exact mathematical ranges for the source C integer predicates.

(defun sslip5g7-is-sint8-p (value)
  (and
   (integerp value)
   (<= -128 value)
   (< value 128)))

(defun sslip5g7-is-sint32-p (value)
  (and
   (integerp value)
   (<= -2147483648 value)
   (< value 2147483648)))

(defun sslip5g7-is-uint64-p (value)
  (and
   (integerp value)
   (<= 0 value)
   (< value 18446744073709551616)))

;; Universal range, identity-on-range, and projection laws for the source C
;; integer conversions used by logical strlen and logical strncmp.

(defun-sk sslip5g7-to-uint64-laws-p ()
  (forall (value)
    (implies
     (integerp value)
     (and
      (sslip5g7-is-uint64-p
       (sslip5g7-to-uint64 value))
      (implies
       (sslip5g7-is-uint64-p value)
       (equal
        (sslip5g7-to-uint64 value)
        value))
      (equal
       (sslip5g7-to-uint64
        (sslip5g7-to-uint64 value))
       (sslip5g7-to-uint64 value))))))

(defun-sk sslip5g7-to-sint32-laws-p ()
  (forall (value)
    (implies
     (integerp value)
     (and
      (sslip5g7-is-sint32-p
       (sslip5g7-to-sint32 value))
      (implies
       (sslip5g7-is-sint32-p value)
       (equal
        (sslip5g7-to-sint32 value)
        value))
      (equal
       (sslip5g7-to-sint32
        (sslip5g7-to-sint32 value))
       (sslip5g7-to-sint32 value))))))

;; Exact unfolding of Memory.valid_rw for the arbitrary allocation map t.

(defun sslip5g7-valid-rw-p (address length)
  (implies
   (< 0 length)
   (and
    (< 0
       (sslip5g7-address-base address))
    (<= 0
        (sslip5g7-address-offset address))
    (<=
     (+ (sslip5g7-address-offset address)
        length)
     (sslip5g7-allocation
      (sslip5g7-address-base address))))))

;; Exact unfolding of A_Strlen.p_valid_str. Its null terminator remains an
;; internal existential over all mathematical integers, and its character
;; range condition remains universally quantified over all integers.

(defun-sk sslip5g7-string-chars-sint8-through-p
    (address bound)
  (forall (position)
    (implies
     (integerp position)
     (implies
      (<= position bound)
      (sslip5g7-is-sint8-p
       (sslip5g7-character-memory
        (sslip5g7-shift address position)))))))

(defun-sk sslip5g7-valid-string-p (address)
  (exists (index)
    (and
     (integerp index)
     (equal
      (sslip5g7-character-memory
       (sslip5g7-shift address index))
      0)
     (sslip5g7-is-uint64-p index)
     (sslip5g7-valid-rw-p
      (sslip5g7-shift address 0)
      (+ 1 index))
     (sslip5g7-string-chars-sint8-through-p
      address index))))

;; Universal closures of A_Strlen.fix_l_strlen and Q_TL_strlen.

(defun-sk sslip5g7-strlen-laws-p ()
  (forall (address)
    (implies
     (sslip5g7-address-p address)
     (and
      (if
          (equal
           (sslip5g7-character-memory
            (sslip5g7-shift address 0))
           0)
          (equal
           (sslip5g7-l-strlen address)
           0)
        (equal
         (sslip5g7-to-uint64
          (+ 1
             (sslip5g7-l-strlen
              (sslip5g7-shift address 1))))
         (sslip5g7-l-strlen address)))
      (sslip5g7-is-uint64-p
       (sslip5g7-l-strlen address))))))

;; Universal closures of A_StrnCmp.fix_l_strncmp_2' and Q_TL_strncmp_2'.

(defun-sk sslip5g7-strncmp-laws-p ()
  (forall (left right count)
    (implies
     (and
      (sslip5g7-address-p left)
      (sslip5g7-address-p right)
      (integerp count))
     (and
      (if
          (equal count 0)
          (equal
           (sslip5g7-l-strncmp left right count)
           0)
        (if
            (equal
             (sslip5g7-character-memory
              (sslip5g7-shift right 0))
             (sslip5g7-character-memory
              (sslip5g7-shift left 0)))
            (if
                (equal
                 (sslip5g7-character-memory
                  (sslip5g7-shift left 0))
                 0)
                (equal
                 (sslip5g7-l-strncmp left right count)
                 0)
              (equal
               (sslip5g7-l-strncmp
                (sslip5g7-shift left 1)
                (sslip5g7-shift right 1)
                (sslip5g7-to-uint64 (- count 1)))
               (sslip5g7-l-strncmp left right count)))
          (equal
           (sslip5g7-to-sint32
            (-
             (sslip5g7-character-memory
              (sslip5g7-shift left 0))
             (sslip5g7-character-memory
              (sslip5g7-shift right 0))))
           (sslip5g7-l-strncmp left right count))))
      (sslip5g7-is-sint32-p
       (sslip5g7-l-strncmp left right count))))))

(defun sslip5g7-strnequal-p (left right count)
  (equal
   (sslip5g7-l-strncmp left right count)
   0))

;; The source prefix hypothesis retains its universal quantifier over every
;; mathematical integer and its original nonnegative and strict upper bounds.

(defun-sk sslip5g7-prefix-equal-before-p
    (left right bound)
  (forall (position)
    (implies
     (integerp position)
     (implies
      (<= 0 position)
      (implies
       (< position bound)
       (equal
        (sslip5g7-character-memory
         (sslip5g7-shift left position))
        (sslip5g7-character-memory
         (sslip5g7-shift right position))))))))

(defun-sk
    ntp4vc-sysfs-streq-loop-inv-5-preserved-goal7-statement ()
  (forall
   (a1 i a)
   (implies
    (and
     (sslip5g7-address-p a1)
     (integerp i)
     (sslip5g7-address-p a)
     (sslip5g7-function-types-p)
     (sslip5g7-to-uint64-laws-p)
     (sslip5g7-to-sint32-laws-p)
     (sslip5g7-strlen-laws-p)
     (sslip5g7-strncmp-laws-p))
    (let*
        ((a2
          (sslip5g7-shift a1 i))
         (x
          (sslip5g7-character-memory a2))
         (a3
          (sslip5g7-shift a i))
         (x1
          (sslip5g7-character-memory a3))
         (x2
          (sslip5g7-l-strlen a)))
      (implies
       (and
        (not (equal x 0))
        (equal x x1)
        (<= i x2)
        (<= i
            (sslip5g7-l-strlen a1))
        (<=
         (sslip5g7-region
          (sslip5g7-address-base a))
         0)
        (<=
         (sslip5g7-region
          (sslip5g7-address-base a1))
         0)
        (sslip5g7-linked-p)
        (sslip5g7-sconst-p)
        (sslip5g7-is-uint64-p i)
        (sslip5g7-valid-string-p a)
        (sslip5g7-valid-string-p a1)
        (sslip5g7-strnequal-p a1 a i)
        (sslip5g7-is-sint8-p x1)
        (sslip5g7-is-sint8-p x)
        (sslip5g7-valid-string-p a3)
        (sslip5g7-valid-string-p a2)
        (sslip5g7-prefix-equal-before-p
         a1 a i))
       (<=
        (sslip5g7-to-uint64 (+ 1 i))
        x2))))))

(value-triple :itpeval-statement-checked)

:q
