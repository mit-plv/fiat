Require Import Program.
Require Export List.
Require Export Tuple.
Require Export String.
Require Export Heading.
Require Export StringBound.

Local Open Scope string_scope.

Local Open Scope Heading_scope.

Definition AlbumHeading := <"Name":: string, "Date":: string, "Year":: nat, "Label":: string, "Country":: string, "UKpeak":: nat, "AUSpeak":: nat, "CANpeak":: nat, "FRApeak":: nat>.

Definition Album := @Tuple AlbumHeading.

Definition Name : Attributes AlbumHeading := {| bindex := "Name" |}.
Definition Date  : Attributes AlbumHeading := {| bindex := "Date" |}.
Definition Year : Attributes AlbumHeading := {| bindex := "Year" |}.
Definition Label : Attributes AlbumHeading := {| bindex := "Label" |}.
Definition Country : Attributes AlbumHeading := {| bindex := "Country" |}.
Definition UKpeak : Attributes AlbumHeading := {| bindex := "UKpeak" |}.
Definition AUSpeak : Attributes AlbumHeading := {| bindex := "AUSpeak" |}.
Definition CANpeak : Attributes AlbumHeading := {| bindex := "CANpeak" |}.
Definition FRApeak : Attributes AlbumHeading := {| bindex := "FRApeak" |}.

Local Open Scope Tuple_scope.

Definition FirstAlbums : list Album := [
  <"Name":: "Please Please Me", "Date":: "22 March 1963", "Year":: 3, "Label":: "Parlophone", "Country":: "UK", "UKpeak":: 1, "AUSpeak":: 0, "CANpeak":: 0, "FRApeak":: 5>;
  <"Name":: "With the Beatles", "Date":: "22 November 1963", "Year":: 3, "Label":: "Parlophone", "Country":: "UK", "UKpeak":: 1, "AUSpeak":: 0, "CANpeak":: 0, "FRApeak":: 5>;
  <"Name":: "Beatlemania! With the Beatles", "Date":: "25 November 1963", "Year":: 3, "Label":: "Capitol", "Country":: "CAN", "UKpeak":: 0, "AUSpeak":: 0, "CANpeak":: 0, "FRApeak":: 0>
].

Definition Albums : list Album := [
  <"Name":: "Please Please Me", "Date":: "22 March 1963", "Year":: 3, "Label":: "Parlophone", "Country":: "UK", "UKpeak":: 1, "AUSpeak":: 0, "CANpeak":: 0, "FRApeak":: 5>;
  <"Name":: "With the Beatles", "Date":: "22 November 1963", "Year":: 3, "Label":: "Parlophone", "Country":: "UK", "UKpeak":: 1, "AUSpeak":: 0, "CANpeak":: 0, "FRApeak":: 5>;
  <"Name":: "Beatlemania! With the Beatles", "Date":: "25 November 1963", "Year":: 3, "Label":: "Capitol", "Country":: "CAN", "UKpeak":: 0, "AUSpeak":: 0, "CANpeak":: 0, "FRApeak":: 0>;
  <"Name":: "Introducing... The Beatles", "Date":: "10 January 1964", "Year":: 4, "Label":: "Vee-Jay", "Country":: "US", "UKpeak":: 0, "AUSpeak":: 0, "CANpeak":: 0, "FRApeak":: 0>;
  <"Name":: "Meet the Beatles!", "Date":: "20 January 1964", "Year":: 4, "Label":: "Capitol", "Country":: "US", "UKpeak":: 0, "AUSpeak":: 0, "CANpeak":: 0, "FRApeak":: 0>;
  <"Name":: "Twist and Shout", "Date":: "3 February 1964", "Year":: 4, "Label":: "Capitol", "Country":: "CAN", "UKpeak":: 0, "AUSpeak":: 0, "CANpeak":: 0, "FRApeak":: 0>;
  <"Name":: "The Beatles' Second Album", "Date":: "10 April 1964", "Year":: 4, "Label":: "Capitol", "Country":: "US", "UKpeak":: 0, "AUSpeak":: 0, "CANpeak":: 0, "FRApeak":: 0>;
  <"Name":: "The Beatles' Long Tall Sally", "Date":: "11 May 1964", "Year":: 4, "Label":: "Capitol", "Country":: "CAN", "UKpeak":: 0, "AUSpeak":: 0, "CANpeak":: 0, "FRApeak":: 0>;
  <"Name":: "A Hard Day's Night", "Date":: "26 June 1964", "Year":: 4, "Label":: "United Artists", "Country":: "US", "UKpeak":: 0, "AUSpeak":: 0, "CANpeak":: 0, "FRApeak":: 5>;
  <"Name":: "A Hard Day's Night", "Date":: "10 July 1964", "Year":: 4, "Label":: "Parlophone", "Country":: "UK", "UKpeak":: 1, "AUSpeak":: 1, "CANpeak":: 0, "FRApeak":: 0>;
  <"Name":: "Something New", "Date":: "20 July 1964", "Year":: 4, "Label":: "Capitol", "Country":: "US", "UKpeak":: 0, "AUSpeak":: 0, "CANpeak":: 0, "FRApeak":: 0>;
  <"Name":: "Beatles for Sale", "Date":: "4 December 1964", "Year":: 4, "Label":: "Parlophone", "Country":: "UK", "UKpeak":: 1, "AUSpeak":: 1, "CANpeak":: 0, "FRApeak":: 0>;
  <"Name":: "Beatles '65", "Date":: "15 December 1964", "Year":: 4, "Label":: "Capitol", "Country":: "US", "UKpeak":: 0, "AUSpeak":: 0, "CANpeak":: 0, "FRApeak":: 80>;
  <"Name":: "Beatles VI", "Date":: "14 June 1965", "Year":: 5, "Label":: "Parlophone", "Country":: "NZ", "UKpeak":: 0, "AUSpeak":: 0, "CANpeak":: 0, "FRApeak":: 0>;
  <"Name":: "Beatles VI", "Date":: "14 June 1965", "Year":: 5, "Label":: "Capitol", "Country":: "US", "UKpeak":: 0, "AUSpeak":: 0, "CANpeak":: 0, "FRApeak":: 0>;
  <"Name":: "Help!", "Date":: "6 August 1965", "Year":: 5, "Label":: "Parlophone", "Country":: "UK", "UKpeak":: 1, "AUSpeak":: 1, "CANpeak":: 0, "FRApeak":: 5>;
  <"Name":: "Help!", "Date":: "13 August 1965", "Year":: 5, "Label":: "Capitol", "Country":: "US", "UKpeak":: 0, "AUSpeak":: 0, "CANpeak":: 0, "FRApeak":: 0>;
  <"Name":: "Rubber Soul", "Date":: "3 December 1965", "Year":: 5, "Label":: "Parlophone", "Country":: "UK", "UKpeak":: 1, "AUSpeak":: 1, "CANpeak":: 0, "FRApeak":: 5>;
  <"Name":: "Rubber Soul", "Date":: "6 December 1965", "Year":: 5, "Label":: "Capitol", "Country":: "US", "UKpeak":: 0, "AUSpeak":: 0, "CANpeak":: 0, "FRApeak":: 0>;
  <"Name":: "Yesterday and Today", "Date":: "15 June 1966", "Year":: 6, "Label":: "Capitol", "Country":: "US", "UKpeak":: 0, "AUSpeak":: 0, "CANpeak":: 0, "FRApeak":: 0>;
  <"Name":: "Revolver", "Date":: "5 August 1966", "Year":: 6, "Label":: "Parlophone", "Country":: "UK", "UKpeak":: 1, "AUSpeak":: 1, "CANpeak":: 0, "FRApeak":: 5>;
  <"Name":: "Revolver", "Date":: "8 August 1966", "Year":: 6, "Label":: "Capitol", "Country":: "US", "UKpeak":: 0, "AUSpeak":: 0, "CANpeak":: 0, "FRApeak":: 0>;
  <"Name":: "Sgt. Pepper's Lonely Hearts Club Band", "Date":: "1 June 1967", "Year":: 7, "Label":: "Capitol", "Country":: "US", "UKpeak":: 1, "AUSpeak":: 1, "CANpeak":: 0, "FRApeak":: 4>;
  <"Name":: "Magical Mystery Tour", "Date":: "27 November 1967", "Year":: 7, "Label":: "Capitol", "Country":: "US", "UKpeak":: 31, "AUSpeak":: 1, "CANpeak":: 0, "FRApeak":: 2>;
  <"Name":: "The Beatles", "Date":: "22 November 1968", "Year":: 8, "Label":: "Capitol", "Country":: "US", "UKpeak":: 1, "AUSpeak":: 1, "CANpeak":: 1, "FRApeak":: 1>;
  <"Name":: "Yellow Submarine", "Date":: "13 January 1969", "Year":: 9, "Label":: "Capitol", "Country":: "US", "UKpeak":: 3, "AUSpeak":: 4, "CANpeak":: 1, "FRApeak":: 4>;
  <"Name":: "Abbey Road", "Date":: "26 September 1969", "Year":: 9, "Label":: "Capitol", "Country":: "US", "UKpeak":: 1, "AUSpeak":: 1, "CANpeak":: 1, "FRApeak":: 1>;
  <"Name":: "Let It Be", "Date":: "8 May 1970", "Year":: 10, "Label":: "United Artists", "Country":: "US", "UKpeak":: 1, "AUSpeak":: 1, "CANpeak":: 1, "FRApeak":: 5>
].

