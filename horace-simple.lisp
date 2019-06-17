;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; horace-simple.lisp
;;
;; based on code by Peter Norvig published in PARADIGMS OF ARTIFICIAL
;; INTELLIGENCE PROGRAMMING, Morgan Kaufmann publishers, 1992.
;;
;; modified for class demonstration by Maria Szegedy
;;

#|

This file contains Common Lisp source code for the HORACE conversation
program. Most of the code is from Peter Norvig, but many changes have
been made to avoid the use of advanced lisp constructs. To run the system
evaluate all of the code in this file and then evaluate (HORACE). The
dialogue may be terminated either by an explicit abort (e.g., command-period
in MCL) or by typing BYE to the HORACE prompt.

|#



;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; variable/binding handling functions
;; (Norvig used association lists and sublis)

(defconstant fail nil
  "Indicates pat-match failure")

(defconstant no-bindings '((t t))
  "Indicates pat-match success, with no variables.")

(defun subvv (varval-list list)
  "Returns list with substitutions made as indicated in in varval-list."
  (dolist (varval-pair varval-list)
    (setq list (subst (second varval-pair) (first varval-pair) list)))
  list)

(defun variable-p (x)
  "Is x a variable (a symbol beginning with `?')?"
  (and (symbolp x)
       (equal (char (symbol-name x) 0)
              #\?)))

(defun segment-pattern-p (pat)
  "Is this a segment-matching pattern: (?*var ...)"
  (and (listp pat)
       (>= (length (symbol-name (car pat))) 2)
       (equal (char (symbol-name (car pat)) 0) #\?)
       (equal (char (symbol-name (car pat)) 1) #\*)))

(defun get-binding (var bindings)
  "Find a (variable value) pair in a binding list."
  (cond ((null bindings) nil)
        ((eq var (caar bindings))
         (car bindings))
        (t (get-binding var (cdr bindings)))))

(defun binding-val (binding)
  "Get the value part of a single binding."
  (cadr binding))

(defun lookup (var bindings)
  "Get the value part (for var) from a binding list."
  (binding-val (get-binding var bindings)))

(defun extend-bindings (var val bindings)
  "Add a (var value) pair to a binding list."
  (cons (list var val)
        ;; Once we add a "real" binding,
        ;; we can get rid of the dummy no-bindings
        (if (eq bindings no-bindings)
            nil
            bindings)))


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; pattern matching

(defun match-variable (var input bindings)
  "Does VAR match input?  Uses (or updates) and returns bindings."
  (let ((binding (get-binding var bindings)))
    (cond ((not binding)
           (extend-bindings var input bindings))
          ((equal input (binding-val binding))
           bindings)
          (t fail))))

(defun pat-match (pattern input &optional (bindings no-bindings))
  "Match pattern against input in the context of the bindings"
  (cond ((eq bindings fail) fail)
        ((variable-p pattern)
         (match-variable pattern input bindings))
        ((equalp pattern input) bindings)
        ((segment-pattern-p pattern)            ; ***
         (segment-match pattern input bindings)); ***
        ((and (listp pattern) (listp input))
         (pat-match (rest pattern)
                    (rest input)
                    (pat-match (first pattern)
                               (first input)
                               bindings)))
        (t fail)))

;; our segment match is not as robust as Norvig's
(defun segment-match (pattern input bindings)
  "Match the segment pattern (?*var remainder) against input."
  (let ((var (first pattern))
        (remainder (rest pattern)))
    (if (null remainder)
      (match-variable var input bindings)
      (if (member (first remainder) input)
        (pat-match remainder
                   (member (first remainder) input)
                   (match-variable var
                                   (upto (first remainder) input)
                                   bindings))
        fail))))


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; utilities

(defun upto (item list)
  "returns the list up to, but not including the first element that is
equalp to the given item."
  (cond ((null list) nil)
        ((equalp item (car list)) nil)
        (t (cons (car list) (upto item (cdr list))))))

(defun flatten (the-list)
  "Append together elements (or lists) in the list."
  (apply #'append
         (mapcar #'(lambda (thing)
                     (if (listp thing)
                       thing
                       (list thing)))
                 the-list)))

(defun random-elt (choices)
  "Choose an element from a list at random."
  (nth (random (length choices)) choices))


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; rule access

(defvar *horace-rules* nil "A list of (pattern responses) lists for HORACE")

(defun rule-pattern (rule) (first rule))

(defun rule-responses (rule) (rest rule))


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; viewpoint switching

;; ours is more complicated than Norvig's because we can't use sublis
;; to do substitutions in parallel
(defun switch-viewpoint (words)
  "Change I to you and vice versa, and so on."
  (subvv '((**I you) (**you I) (**me you) (**am are))
          (subvv '((I **I) (you **you) (me **me) (am **am))
                 words)))


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; top level

(defun use-horace-rules (input)
  "Find some rule with which to transform the input."
  (let ((match-result nil)(matching-rule nil))
    ;; find the matching rule
    (dolist (rule *horace-rules*)
      (unless matching-rule
        (setq match-result
              (pat-match (rule-pattern rule) input))
        (if (not (eq match-result fail))
          (setq matching-rule rule))))
    ;; return the result of the substitutions
    (subvv (switch-viewpoint match-result)
           (random-elt
            (rule-responses matching-rule)))))


#|
;; the simplest version of the interpreter
;; doesn't like punctuation and requires list input
(defun horace ()
  "Respond to user input using pattern matching rules."
  (loop
    (print 'horace>)
    (print (flatten (use-horace-rules (read))))))
|#


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; better I/O

(defun read-line-no-punct ()
  "Read an input line, ignoring punctuation."
  (read-from-string
    (concatenate
     'string
     "(" (substitute-if #\space #'punctuation-p
                        (read-line))
     ")")))

(defun punctuation-p (char)
  (find char ".,;:`!?#-()\\\""))

(defun horace ()
  "Respond to user input using pattern matching rules."
  (loop
    (print 'horace>)
    (let* ((input (read-line-no-punct))
           (response (flatten (use-horace-rules input))))
      (print-with-spaces response)
      (if (or (equal response '(bye))
              (equal response '(good bye))
              (equal response '(vale))) (RETURN)))))

(defun print-with-spaces (list)
  (format t "~{~a ~}" list))


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; sample rule set

(setq *horace-rules*
 '(((?*x hello ?*y)
    (How do you do.  I will tell you about my poem Ode I.IX.))
   ((?*x salve ?*y)
    (Quid agis.  I will tell you about my poem Ode I.IX.))
   ((?*x who are you ?*y)
    (I am the great Roman poet Horace.  I write poems on behalf of Augustus
     Caesar himself.))
   ((?*x whole poem ?*y)
    (I would say the poem is about how you should seize the day. Live in the
     present! Flee from asking what tomorrow brings! Drink wine instead.))
   ((?*x poem ?*y about ?*y)
    (I would say the poem is about how you should seize the day. Live in the
     present! Flee from asking what tomorrow brings! Drink wine instead.))
   ((?*x first stanza ?*y)
    (The first stanza introduces outside chilliness frigus next to which to
     contrast the sort of living I advise.))
   ((?*x second stanza ?*y)
    (The second stanza finishes the contrast with the picture of outside warmth
     and addresses Thaliarchus.))
   ((?*x third stanza ?*y)
    (In the third stanza I call upon the reader to ignore the harshness of the
     outside world and to leave it to the gods.))
   ((?*x fourth stanza ?*y)
    (The fourth stanza is the famous part where I once again compel the
     listener to forget the future and focus on the present especially love.))
   ((?*x fifth stanza ?*y)
    (The fifth stanza bridges the fourth and sixth stanzas by shifting the
     focus from uncomfortable old age to the girl that Thaliarchus is bound to
     meet on the Campus.))
   ((?*x sixth stanza ?*y)
    (The sixth stanza reminds Thaliarchus of one of my favorite subjects
     namely love personified as a girl hiding away in the darkest corner.))
   ((?*x wine ?*y)
    (In my works wine represents life or at least vital living. Here it
     represents enjoyment of life mentioned in the second stanza.))
   ((?*x gods ?*y)
    (The gods here are contrasted with humans. The future is the business of
     the gods while the present is the business of the humans. I mention the
     gods in the third stanza.))
   ((?*x love ?*y)
    (Love is perhaps my favorite thing about life and in this poem it is what
     I use to convince Thaliarchus to pay attention to life. The convincing is
     done mainly in stanzas IV through VI.))
   ((?*x age ?*y)
    (Age and mortality should not be of any concern to a human. We have to live
     in the present! I make sure to say so in the fifth stanza.))
   ((?*x life ?*y)
    (Life is a privilege we as humans get to experience. Make sure to use it to
     its full extent. Do not worry about what comes after.))
   ((?*x afterlife ?*y)
    (It is pointless to talk about the afterlife since we know nothing about
     it. I prefer livelier subjects.))
   ((?*x Thaliarchus ?*y)
    (Thaliarchus was a friend of mine who I felt needed this poem. I refer to
     him by name in the second stanza.))
   ((bye)
    (Vale!))
   ((vale)
    (Vale!))
   ((?*x)
    (I am not sure I understand you fully)
    (Do you have any questions about the poem?)
    (Please continue)
    (Go on))))

; (format t "~%Type (HORACE) to run HORACE. Type BYE to quit HORACE.~%")
(horace)
