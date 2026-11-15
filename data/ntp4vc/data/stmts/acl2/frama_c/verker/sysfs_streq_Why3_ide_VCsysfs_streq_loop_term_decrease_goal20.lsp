;; Statement-only formalization of NTP4VC corpus artifact
;; frama_c/verker/sysfs_streq_Why3_ide_VCsysfs_streq_loop_term_decrease_goal20:
;; the sysfs string-equality loop's unsigned successor index is strictly
;; greater than its current index, under the stated equal-character, memory,
;; valid-string, comparison, region, linkedness, constancy, and prefix
;; hypotheses. This file contains no proof.

(in-package "ACL2")

(set-inhibit-output-lst '(prove proof-tree event summary))

;; Source addresses are exactly pairs of mathematical integers.

(defun ssltdg20-address-p (address)
  (and
   (consp address)
   (integerp (car address))
   (integerp (cdr address))))

(defun ssltdg20-address-base (address)
  (car address))

(defun ssltdg20-address-offset (address)
  (cdr address))

(defun ssltdg20-shift (address amount)
  (cons
   (ssltdg20-address-base address)
   (+ (ssltdg20-address-offset address)
      amount)))

;; Conservative interfaces represent the universally arbitrary character
;; memory t_1 and allocation map t, together with the source region, logical
;; strlen, logical strncmp, C integer conversions, linkedness, and constancy
;; symbols.

(defstub ssltdg20-character-memory (address) t)
(defstub ssltdg20-allocation (index) t)
(defstub ssltdg20-region (base) t)
(defstub ssltdg20-l-strlen (address) t)
(defstub ssltdg20-l-strncmp (left right count) t)
(defstub ssltdg20-to-uint64 (value) t)
(defstub ssltdg20-to-sint32 (value) t)
(defstub ssltdg20-linked-op () t)
(defstub ssltdg20-sconst-op () t)

;; Preserve the source function types over the full address and unbounded
;; mathematical-integer domains.

(defun-sk ssltdg20-function-types-p ()
  (forall (address index base value left right count)
    (and
     (implies
      (ssltdg20-address-p address)
      (and
       (integerp
        (ssltdg20-character-memory address))
       (integerp
        (ssltdg20-l-strlen address))))
     (implies
      (integerp index)
      (integerp
       (ssltdg20-allocation index)))
     (implies
      (integerp base)
      (integerp
       (ssltdg20-region base)))
     (implies
      (integerp value)
      (and
       (integerp
        (ssltdg20-to-uint64 value))
       (integerp
        (ssltdg20-to-sint32 value))))
     (implies
      (and
       (ssltdg20-address-p left)
       (ssltdg20-address-p right)
       (integerp count))
      (integerp
       (ssltdg20-l-strncmp left right count))))))

(defun ssltdg20-linked-p ()
  (if (ssltdg20-linked-op) t nil))

(defun ssltdg20-sconst-p ()
  (if (ssltdg20-sconst-op) t nil))

;; Exact mathematical ranges for the source C integer predicates.

(defun ssltdg20-is-sint8-p (value)
  (and
   (integerp value)
   (<= -128 value)
   (< value 128)))

(defun ssltdg20-is-sint32-p (value)
  (and
   (integerp value)
   (<= -2147483648 value)
   (< value 2147483648)))

(defun ssltdg20-is-uint64-p (value)
  (and
   (integerp value)
   (<= 0 value)
   (< value 18446744073709551616)))

;; Universal range, identity-on-range, and projection laws for the source C
;; integer conversions used by logical strlen and logical strncmp.

(defun-sk ssltdg20-to-uint64-laws-p ()
  (forall (value)
    (implies
     (integerp value)
     (and
      (ssltdg20-is-uint64-p
       (ssltdg20-to-uint64 value))
      (implies
       (ssltdg20-is-uint64-p value)
       (equal
        (ssltdg20-to-uint64 value)
        value))
      (equal
       (ssltdg20-to-uint64
        (ssltdg20-to-uint64 value))
       (ssltdg20-to-uint64 value))))))

(defun-sk ssltdg20-to-sint32-laws-p ()
  (forall (value)
    (implies
     (integerp value)
     (and
      (ssltdg20-is-sint32-p
       (ssltdg20-to-sint32 value))
      (implies
       (ssltdg20-is-sint32-p value)
       (equal
        (ssltdg20-to-sint32 value)
        value))
      (equal
       (ssltdg20-to-sint32
        (ssltdg20-to-sint32 value))
       (ssltdg20-to-sint32 value))))))

;; Exact unfolding of Memory.valid_rw for the arbitrary allocation map t.

(defun ssltdg20-valid-rw-p (address length)
  (implies
   (< 0 length)
   (and
    (< 0
       (ssltdg20-address-base address))
    (<= 0
        (ssltdg20-address-offset address))
    (<=
     (+ (ssltdg20-address-offset address)
        length)
     (ssltdg20-allocation
      (ssltdg20-address-base address))))))

;; Exact unfolding of A_Strlen.p_valid_str. Its null terminator remains an
;; internal existential over all mathematical integers, and its character
;; range condition remains universally quantified over all integers.

(defun-sk ssltdg20-string-chars-sint8-through-p
    (address bound)
  (forall (position)
    (implies
     (integerp position)
     (implies
      (<= position bound)
      (ssltdg20-is-sint8-p
       (ssltdg20-character-memory
        (ssltdg20-shift address position)))))))

(defun-sk ssltdg20-valid-string-p (address)
  (exists (index)
    (and
     (integerp index)
     (equal
      (ssltdg20-character-memory
       (ssltdg20-shift address index))
      0)
     (ssltdg20-is-uint64-p index)
     (ssltdg20-valid-rw-p
      (ssltdg20-shift address 0)
      (+ 1 index))
     (ssltdg20-string-chars-sint8-through-p
      address index))))

;; Universal closures of A_Strlen.fix_l_strlen and Q_TL_strlen.

(defun-sk ssltdg20-strlen-laws-p ()
  (forall (address)
    (implies
     (ssltdg20-address-p address)
     (and
      (if
          (equal
           (ssltdg20-character-memory
            (ssltdg20-shift address 0))
           0)
          (equal
           (ssltdg20-l-strlen address)
           0)
        (equal
         (ssltdg20-to-uint64
          (+ 1
             (ssltdg20-l-strlen
              (ssltdg20-shift address 1))))
         (ssltdg20-l-strlen address)))
      (ssltdg20-is-uint64-p
       (ssltdg20-l-strlen address))))))

;; Universal closures of A_StrnCmp.fix_l_strncmp_2' and Q_TL_strncmp_2'.

(defun-sk ssltdg20-strncmp-laws-p ()
  (forall (left right count)
    (implies
     (and
      (ssltdg20-address-p left)
      (ssltdg20-address-p right)
      (integerp count))
     (and
      (if
          (equal count 0)
          (equal
           (ssltdg20-l-strncmp left right count)
           0)
        (if
            (equal
             (ssltdg20-character-memory
              (ssltdg20-shift right 0))
             (ssltdg20-character-memory
              (ssltdg20-shift left 0)))
            (if
                (equal
                 (ssltdg20-character-memory
                  (ssltdg20-shift left 0))
                 0)
                (equal
                 (ssltdg20-l-strncmp left right count)
                 0)
              (equal
               (ssltdg20-l-strncmp
                (ssltdg20-shift left 1)
                (ssltdg20-shift right 1)
                (ssltdg20-to-uint64 (- count 1)))
               (ssltdg20-l-strncmp left right count)))
          (equal
           (ssltdg20-to-sint32
            (-
             (ssltdg20-character-memory
              (ssltdg20-shift left 0))
             (ssltdg20-character-memory
              (ssltdg20-shift right 0))))
           (ssltdg20-l-strncmp left right count))))
      (ssltdg20-is-sint32-p
       (ssltdg20-l-strncmp left right count))))))

(defun ssltdg20-strnequal-p (left right count)
  (equal
   (ssltdg20-l-strncmp left right count)
   0))

;; The source prefix hypothesis retains its universal quantifier over every
;; mathematical integer and its original nonnegative and strict upper bounds.

(defun-sk ssltdg20-prefix-equal-before-p
    (left right bound)
  (forall (position)
    (implies
     (integerp position)
     (implies
      (<= 0 position)
      (implies
       (< position bound)
       (equal
        (ssltdg20-character-memory
         (ssltdg20-shift left position))
        (ssltdg20-character-memory
         (ssltdg20-shift right position))))))))

(defun-sk
    ntp4vc-sysfs-streq-loop-term-decrease-goal20-statement ()
  (forall
   (a1 i a)
   (implies
    (and
     (ssltdg20-address-p a1)
     (integerp i)
     (ssltdg20-address-p a)
     (ssltdg20-function-types-p)
     (ssltdg20-to-uint64-laws-p)
     (ssltdg20-to-sint32-laws-p)
     (ssltdg20-strlen-laws-p)
     (ssltdg20-strncmp-laws-p))
    (let*
        ((a2
          (ssltdg20-shift a1 i))
         (x
          (ssltdg20-character-memory a2))
         (a3
          (ssltdg20-shift a i))
         (x1
          (ssltdg20-character-memory a3)))
      (implies
       (and
        (not (equal x 0))
        (equal x x1)
        (<= i
            (ssltdg20-l-strlen a))
        (<= i
            (ssltdg20-l-strlen a1))
        (<=
         (ssltdg20-region
          (ssltdg20-address-base a))
         0)
        (<=
         (ssltdg20-region
          (ssltdg20-address-base a1))
         0)
        (ssltdg20-linked-p)
        (ssltdg20-sconst-p)
        (ssltdg20-is-uint64-p i)
        (ssltdg20-valid-string-p a)
        (ssltdg20-valid-string-p a1)
        (ssltdg20-strnequal-p a1 a i)
        (ssltdg20-is-sint8-p x1)
        (ssltdg20-is-sint8-p x)
        (ssltdg20-valid-string-p a3)
        (ssltdg20-valid-string-p a2)
        (ssltdg20-prefix-equal-before-p
         a1 a i))
       (< i
          (ssltdg20-to-uint64 (+ 1 i))))))))

(value-triple :itpeval-statement-checked)

:q
