;; Statement-only formalization of NTP4VC corpus artifact
;; frama_c/verker/sysfs_streq_Why3_ide_VCsysfs_streq_loop_inv_7_preserved_goal10:
;; preservation of bounded string-prefix equality after extending a shared
;; nonzero equal-character prefix by one, under the stated memory, string,
;; comparison, region, linkedness, constancy, and loop-prefix hypotheses.
;; This file contains no proof.

(in-package "ACL2")

(set-inhibit-output-lst '(prove proof-tree event summary))

;; Source addresses are exactly pairs of mathematical integers.

(defun sslip7g10-address-p (address)
  (and
   (consp address)
   (integerp (car address))
   (integerp (cdr address))))

(defun sslip7g10-address-base (address)
  (car address))

(defun sslip7g10-address-offset (address)
  (cdr address))

(defun sslip7g10-shift (address amount)
  (cons
   (sslip7g10-address-base address)
   (+ (sslip7g10-address-offset address)
      amount)))

;; Conservative interfaces represent the universally arbitrary character
;; memory t_1 and allocation map t, together with the source region, logical
;; strlen, logical strncmp, C integer conversions, linkedness, and constancy
;; symbols.

(defstub sslip7g10-character-memory (address) t)
(defstub sslip7g10-allocation (index) t)
(defstub sslip7g10-region (base) t)
(defstub sslip7g10-l-strlen (address) t)
(defstub sslip7g10-l-strncmp (left right count) t)
(defstub sslip7g10-to-uint64 (value) t)
(defstub sslip7g10-to-sint32 (value) t)
(defstub sslip7g10-linked-op () t)
(defstub sslip7g10-sconst-op () t)

;; Preserve the source function types over the full address and unbounded
;; mathematical-integer domains.

(defun-sk sslip7g10-function-types-p ()
  (forall (address index base value left right count)
    (and
     (implies
      (sslip7g10-address-p address)
      (and
       (integerp
        (sslip7g10-character-memory address))
       (integerp
        (sslip7g10-l-strlen address))))
     (implies
      (integerp index)
      (integerp
       (sslip7g10-allocation index)))
     (implies
      (integerp base)
      (integerp
       (sslip7g10-region base)))
     (implies
      (integerp value)
      (and
       (integerp
        (sslip7g10-to-uint64 value))
       (integerp
        (sslip7g10-to-sint32 value))))
     (implies
      (and
       (sslip7g10-address-p left)
       (sslip7g10-address-p right)
       (integerp count))
      (integerp
       (sslip7g10-l-strncmp left right count))))))

(defun sslip7g10-linked-p ()
  (if (sslip7g10-linked-op) t nil))

(defun sslip7g10-sconst-p ()
  (if (sslip7g10-sconst-op) t nil))

;; Exact mathematical ranges for the source C integer predicates.

(defun sslip7g10-is-sint8-p (value)
  (and
   (integerp value)
   (<= -128 value)
   (< value 128)))

(defun sslip7g10-is-sint32-p (value)
  (and
   (integerp value)
   (<= -2147483648 value)
   (< value 2147483648)))

(defun sslip7g10-is-uint64-p (value)
  (and
   (integerp value)
   (<= 0 value)
   (< value 18446744073709551616)))

;; Universal range, identity-on-range, and projection laws for the source C
;; integer conversions used by logical strlen and logical strncmp.

(defun-sk sslip7g10-to-uint64-laws-p ()
  (forall (value)
    (implies
     (integerp value)
     (and
      (sslip7g10-is-uint64-p
       (sslip7g10-to-uint64 value))
      (implies
       (sslip7g10-is-uint64-p value)
       (equal
        (sslip7g10-to-uint64 value)
        value))
      (equal
       (sslip7g10-to-uint64
        (sslip7g10-to-uint64 value))
       (sslip7g10-to-uint64 value))))))

(defun-sk sslip7g10-to-sint32-laws-p ()
  (forall (value)
    (implies
     (integerp value)
     (and
      (sslip7g10-is-sint32-p
       (sslip7g10-to-sint32 value))
      (implies
       (sslip7g10-is-sint32-p value)
       (equal
        (sslip7g10-to-sint32 value)
        value))
      (equal
       (sslip7g10-to-sint32
        (sslip7g10-to-sint32 value))
       (sslip7g10-to-sint32 value))))))

;; Exact unfolding of Memory.valid_rw for the arbitrary allocation map t.

(defun sslip7g10-valid-rw-p (address length)
  (implies
   (< 0 length)
   (and
    (< 0
       (sslip7g10-address-base address))
    (<= 0
        (sslip7g10-address-offset address))
    (<=
     (+ (sslip7g10-address-offset address)
        length)
     (sslip7g10-allocation
      (sslip7g10-address-base address))))))

;; Exact unfolding of A_Strlen.p_valid_str. Its null terminator remains an
;; internal existential over all mathematical integers, and its character
;; range condition remains universally quantified over all integers.

(defun-sk sslip7g10-string-chars-sint8-through-p
    (address bound)
  (forall (position)
    (implies
     (integerp position)
     (implies
      (<= position bound)
      (sslip7g10-is-sint8-p
       (sslip7g10-character-memory
        (sslip7g10-shift address position)))))))

(defun-sk sslip7g10-valid-string-p (address)
  (exists (index)
    (and
     (integerp index)
     (equal
      (sslip7g10-character-memory
       (sslip7g10-shift address index))
      0)
     (sslip7g10-is-uint64-p index)
     (sslip7g10-valid-rw-p
      (sslip7g10-shift address 0)
      (+ 1 index))
     (sslip7g10-string-chars-sint8-through-p
      address index))))

;; Universal closures of A_Strlen.fix_l_strlen and Q_TL_strlen.

(defun-sk sslip7g10-strlen-laws-p ()
  (forall (address)
    (implies
     (sslip7g10-address-p address)
     (and
      (if
          (equal
           (sslip7g10-character-memory
            (sslip7g10-shift address 0))
           0)
          (equal
           (sslip7g10-l-strlen address)
           0)
        (equal
         (sslip7g10-to-uint64
          (+ 1
             (sslip7g10-l-strlen
              (sslip7g10-shift address 1))))
         (sslip7g10-l-strlen address)))
      (sslip7g10-is-uint64-p
       (sslip7g10-l-strlen address))))))

;; Universal closures of A_StrnCmp.fix_l_strncmp_2' and Q_TL_strncmp_2'.

(defun-sk sslip7g10-strncmp-laws-p ()
  (forall (left right count)
    (implies
     (and
      (sslip7g10-address-p left)
      (sslip7g10-address-p right)
      (integerp count))
     (and
      (if
          (equal count 0)
          (equal
           (sslip7g10-l-strncmp left right count)
           0)
        (if
            (equal
             (sslip7g10-character-memory
              (sslip7g10-shift right 0))
             (sslip7g10-character-memory
              (sslip7g10-shift left 0)))
            (if
                (equal
                 (sslip7g10-character-memory
                  (sslip7g10-shift left 0))
                 0)
                (equal
                 (sslip7g10-l-strncmp left right count)
                 0)
              (equal
               (sslip7g10-l-strncmp
                (sslip7g10-shift left 1)
                (sslip7g10-shift right 1)
                (sslip7g10-to-uint64 (- count 1)))
               (sslip7g10-l-strncmp left right count)))
          (equal
           (sslip7g10-to-sint32
            (-
             (sslip7g10-character-memory
              (sslip7g10-shift left 0))
             (sslip7g10-character-memory
              (sslip7g10-shift right 0))))
           (sslip7g10-l-strncmp left right count))))
      (sslip7g10-is-sint32-p
       (sslip7g10-l-strncmp left right count))))))

(defun sslip7g10-strnequal-p (left right count)
  (equal
   (sslip7g10-l-strncmp left right count)
   0))

;; The source prefix hypothesis retains its universal quantifier over every
;; mathematical integer and its original nonnegative and strict upper bounds.

(defun-sk sslip7g10-prefix-equal-before-p
    (left right bound)
  (forall (position)
    (implies
     (integerp position)
     (implies
      (<= 0 position)
      (implies
       (< position bound)
       (equal
        (sslip7g10-character-memory
         (sslip7g10-shift left position))
        (sslip7g10-character-memory
         (sslip7g10-shift right position))))))))

(defun-sk
    ntp4vc-sysfs-streq-loop-inv-7-preserved-goal10-statement ()
  (forall
   (a1 i a)
   (implies
    (and
     (sslip7g10-address-p a1)
     (integerp i)
     (sslip7g10-address-p a)
     (sslip7g10-function-types-p)
     (sslip7g10-to-uint64-laws-p)
     (sslip7g10-to-sint32-laws-p)
     (sslip7g10-strlen-laws-p)
     (sslip7g10-strncmp-laws-p))
    (let*
        ((a2
          (sslip7g10-shift a1 i))
         (x
          (sslip7g10-character-memory a2))
         (a3
          (sslip7g10-shift a i))
         (x1
          (sslip7g10-character-memory a3)))
      (implies
       (and
        (not (equal x 0))
        (equal x x1)
        (<= i
            (sslip7g10-l-strlen a))
        (<= i
            (sslip7g10-l-strlen a1))
        (<=
         (sslip7g10-region
          (sslip7g10-address-base a))
         0)
        (<=
         (sslip7g10-region
          (sslip7g10-address-base a1))
         0)
        (sslip7g10-linked-p)
        (sslip7g10-sconst-p)
        (sslip7g10-is-uint64-p i)
        (sslip7g10-valid-string-p a)
        (sslip7g10-valid-string-p a1)
        (sslip7g10-strnequal-p a1 a i)
        (sslip7g10-is-sint8-p x1)
        (sslip7g10-is-sint8-p x)
        (sslip7g10-valid-string-p a3)
        (sslip7g10-valid-string-p a2)
        (sslip7g10-prefix-equal-before-p
         a1 a i))
       (sslip7g10-strnequal-p
        a1
        a
        (sslip7g10-to-uint64 (+ 1 i))))))))

(value-triple :itpeval-statement-checked)

:q
