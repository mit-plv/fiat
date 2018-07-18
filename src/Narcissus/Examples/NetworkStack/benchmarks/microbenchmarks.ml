open Core_bench.Std
open Fiat4Mirage

let buf = Array.make 4096 0L
let must = function Some x -> x | None -> failwith "Unexpected: 'None'"

let arp_request_ether_decode_42_input = ArrayVector.of_array [|72L;81L;183L;14L;152L;89L;80L;199L;191L;62L;218L;205L;8L;6L;0L;1L;8L;0L;6L;4L;0L;1L;80L;199L;191L;62L;218L;205L;192L;168L;1L;1L;0L;0L;0L;0L;0L;0L;192L;168L;1L;109L|]

let arp_request_ether_encode_42_input = must (Fiat4Mirage.fiat_ethernet_decode 42 arp_request_ether_decode_42_input 42)

let arp_request_arp_decode_28_input = ArrayVector.of_array [|0L;1L;8L;0L;6L;4L;0L;1L;80L;199L;191L;62L;218L;205L;192L;168L;1L;1L;0L;0L;0L;0L;0L;0L;192L;168L;1L;109L|]

let arp_request_arp_encode_28_input = must (Fiat4Mirage.fiat_arp_decode 28 arp_request_arp_decode_28_input)

let arp_response_ether_decode_42_input = ArrayVector.of_array [|80L;199L;191L;62L;218L;205L;72L;81L;183L;14L;152L;89L;8L;6L;0L;1L;8L;0L;6L;4L;0L;2L;72L;81L;183L;14L;152L;89L;192L;168L;1L;109L;80L;199L;191L;62L;218L;205L;192L;168L;1L;1L|]

let arp_response_ether_encode_42_input = must (Fiat4Mirage.fiat_ethernet_decode 42 arp_response_ether_decode_42_input 42)

let arp_response_arp_decode_28_input = ArrayVector.of_array [|0L;1L;8L;0L;6L;4L;0L;2L;72L;81L;183L;14L;152L;89L;192L;168L;1L;109L;80L;199L;191L;62L;218L;205L;192L;168L;1L;1L|]

let arp_response_arp_encode_28_input = must (Fiat4Mirage.fiat_arp_decode 28 arp_response_arp_decode_28_input)

let http_request_ether_decode_141_input = ArrayVector.of_array [|80L;199L;191L;62L;218L;205L;72L;81L;183L;14L;152L;89L;8L;0L;69L;0L;0L;127L;27L;241L;64L;0L;64L;6L;67L;105L;192L;168L;1L;109L;151L;101L;129L;164L;144L;42L;0L;80L;19L;125L;120L;241L;243L;111L;68L;47L;128L;24L;0L;229L;29L;216L;0L;0L;1L;1L;8L;10L;228L;110L;2L;137L;80L;206L;41L;110L;71L;69L;84L;32L;47L;32L;72L;84L;84L;80L;47L;49L;46L;49L;13L;10L;72L;111L;115L;116L;58L;32L;110L;121L;116L;105L;109L;101L;115L;46L;99L;111L;109L;13L;10L;85L;115L;101L;114L;45L;65L;103L;101L;110L;116L;58L;32L;99L;117L;114L;108L;47L;55L;46L;52L;55L;46L;48L;13L;10L;65L;99L;99L;101L;112L;116L;58L;32L;42L;47L;42L;13L;10L;13L;10L|]

let http_request_ether_encode_141_input = must (Fiat4Mirage.fiat_ethernet_decode 141 http_request_ether_decode_141_input 141)

let http_request_ip_decode_127_input = ArrayVector.of_array [|69L;0L;0L;127L;27L;241L;64L;0L;64L;6L;67L;105L;192L;168L;1L;109L;151L;101L;129L;164L;144L;42L;0L;80L;19L;125L;120L;241L;243L;111L;68L;47L;128L;24L;0L;229L;29L;216L;0L;0L;1L;1L;8L;10L;228L;110L;2L;137L;80L;206L;41L;110L;71L;69L;84L;32L;47L;32L;72L;84L;84L;80L;47L;49L;46L;49L;13L;10L;72L;111L;115L;116L;58L;32L;110L;121L;116L;105L;109L;101L;115L;46L;99L;111L;109L;13L;10L;85L;115L;101L;114L;45L;65L;103L;101L;110L;116L;58L;32L;99L;117L;114L;108L;47L;55L;46L;52L;55L;46L;48L;13L;10L;65L;99L;99L;101L;112L;116L;58L;32L;42L;47L;42L;13L;10L;13L;10L|]

let http_request_ip_encode_127_input = must (Fiat4Mirage.fiat_ipv4_decode 127 http_request_ip_decode_127_input)

let http_request_tcp_decode_107_input = ArrayVector.of_array [|144L;42L;0L;80L;19L;125L;120L;241L;243L;111L;68L;47L;128L;24L;0L;229L;29L;216L;0L;0L;1L;1L;8L;10L;228L;110L;2L;137L;80L;206L;41L;110L;71L;69L;84L;32L;47L;32L;72L;84L;84L;80L;47L;49L;46L;49L;13L;10L;72L;111L;115L;116L;58L;32L;110L;121L;116L;105L;109L;101L;115L;46L;99L;111L;109L;13L;10L;85L;115L;101L;114L;45L;65L;103L;101L;110L;116L;58L;32L;99L;117L;114L;108L;47L;55L;46L;52L;55L;46L;48L;13L;10L;65L;99L;99L;101L;112L;116L;58L;32L;42L;47L;42L;13L;10L;13L;10L|]

let http_request_tcp_encode_107_input = must (Fiat4Mirage.fiat_tcp_decode 107 http_request_tcp_decode_107_input (ArrayVector.of_array [|192L;168L;1L;109L|]) (ArrayVector.of_array [|151L;101L;129L;164L|]) (107L))

let http_response_ether_decode_372_input = ArrayVector.of_array [|72L;81L;183L;14L;152L;89L;80L;199L;191L;62L;218L;205L;8L;0L;69L;32L;1L;102L;109L;95L;64L;0L;59L;6L;245L;243L;151L;101L;129L;164L;192L;168L;1L;109L;0L;80L;144L;42L;243L;111L;68L;47L;19L;125L;121L;60L;128L;24L;0L;55L;33L;1L;0L;0L;1L;1L;8L;10L;80L;206L;41L;115L;228L;110L;2L;137L;72L;84L;84L;80L;47L;49L;46L;49L;32L;51L;48L;49L;32L;77L;111L;118L;101L;100L;32L;80L;101L;114L;109L;97L;110L;101L;110L;116L;108L;121L;13L;10L;83L;101L;114L;118L;101L;114L;58L;32L;86L;97L;114L;110L;105L;115L;104L;13L;10L;82L;101L;116L;114L;121L;45L;65L;102L;116L;101L;114L;58L;32L;48L;13L;10L;67L;111L;110L;116L;101L;110L;116L;45L;76L;101L;110L;103L;116L;104L;58L;32L;48L;13L;10L;76L;111L;99L;97L;116L;105L;111L;110L;58L;32L;104L;116L;116L;112L;115L;58L;47L;47L;119L;119L;119L;46L;110L;121L;116L;105L;109L;101L;115L;46L;99L;111L;109L;47L;13L;10L;65L;99L;99L;101L;112L;116L;45L;82L;97L;110L;103L;101L;115L;58L;32L;98L;121L;116L;101L;115L;13L;10L;68L;97L;116L;101L;58L;32L;84L;104L;117L;44L;32L;49L;50L;32L;74L;117L;108L;32L;50L;48L;49L;56L;32L;48L;49L;58L;52L;54L;58L;49L;57L;32L;71L;77L;84L;13L;10L;88L;45L;83L;101L;114L;118L;101L;100L;45L;66L;121L;58L;32L;99L;97L;99L;104L;101L;45L;98L;111L;115L;56L;50L;51L;48L;45L;66L;79L;83L;13L;10L;88L;45L;67L;97L;99L;104L;101L;58L;32L;72L;73L;84L;13L;10L;88L;45L;67L;97L;99L;104L;101L;45L;72L;105L;116L;115L;58L;32L;48L;13L;10L;88L;45L;70L;114L;97L;109L;101L;45L;79L;112L;116L;105L;111L;110L;115L;58L;32L;68L;69L;78L;89L;13L;10L;67L;111L;110L;110L;101L;99L;116L;105L;111L;110L;58L;32L;99L;108L;111L;115L;101L;13L;10L;88L;45L;65L;80L;73L;45L;86L;101L;114L;115L;105L;111L;110L;58L;32L;70L;45L;48L;13L;10L;13L;10L|]

let http_response_ether_encode_372_input = must (Fiat4Mirage.fiat_ethernet_decode 372 http_response_ether_decode_372_input 372)

let http_response_ip_decode_358_input = ArrayVector.of_array [|69L;32L;1L;102L;109L;95L;64L;0L;59L;6L;245L;243L;151L;101L;129L;164L;192L;168L;1L;109L;0L;80L;144L;42L;243L;111L;68L;47L;19L;125L;121L;60L;128L;24L;0L;55L;33L;1L;0L;0L;1L;1L;8L;10L;80L;206L;41L;115L;228L;110L;2L;137L;72L;84L;84L;80L;47L;49L;46L;49L;32L;51L;48L;49L;32L;77L;111L;118L;101L;100L;32L;80L;101L;114L;109L;97L;110L;101L;110L;116L;108L;121L;13L;10L;83L;101L;114L;118L;101L;114L;58L;32L;86L;97L;114L;110L;105L;115L;104L;13L;10L;82L;101L;116L;114L;121L;45L;65L;102L;116L;101L;114L;58L;32L;48L;13L;10L;67L;111L;110L;116L;101L;110L;116L;45L;76L;101L;110L;103L;116L;104L;58L;32L;48L;13L;10L;76L;111L;99L;97L;116L;105L;111L;110L;58L;32L;104L;116L;116L;112L;115L;58L;47L;47L;119L;119L;119L;46L;110L;121L;116L;105L;109L;101L;115L;46L;99L;111L;109L;47L;13L;10L;65L;99L;99L;101L;112L;116L;45L;82L;97L;110L;103L;101L;115L;58L;32L;98L;121L;116L;101L;115L;13L;10L;68L;97L;116L;101L;58L;32L;84L;104L;117L;44L;32L;49L;50L;32L;74L;117L;108L;32L;50L;48L;49L;56L;32L;48L;49L;58L;52L;54L;58L;49L;57L;32L;71L;77L;84L;13L;10L;88L;45L;83L;101L;114L;118L;101L;100L;45L;66L;121L;58L;32L;99L;97L;99L;104L;101L;45L;98L;111L;115L;56L;50L;51L;48L;45L;66L;79L;83L;13L;10L;88L;45L;67L;97L;99L;104L;101L;58L;32L;72L;73L;84L;13L;10L;88L;45L;67L;97L;99L;104L;101L;45L;72L;105L;116L;115L;58L;32L;48L;13L;10L;88L;45L;70L;114L;97L;109L;101L;45L;79L;112L;116L;105L;111L;110L;115L;58L;32L;68L;69L;78L;89L;13L;10L;67L;111L;110L;110L;101L;99L;116L;105L;111L;110L;58L;32L;99L;108L;111L;115L;101L;13L;10L;88L;45L;65L;80L;73L;45L;86L;101L;114L;115L;105L;111L;110L;58L;32L;70L;45L;48L;13L;10L;13L;10L|]

let http_response_ip_encode_358_input = must (Fiat4Mirage.fiat_ipv4_decode 358 http_response_ip_decode_358_input)

let http_response_tcp_decode_338_input = ArrayVector.of_array [|0L;80L;144L;42L;243L;111L;68L;47L;19L;125L;121L;60L;128L;24L;0L;55L;33L;1L;0L;0L;1L;1L;8L;10L;80L;206L;41L;115L;228L;110L;2L;137L;72L;84L;84L;80L;47L;49L;46L;49L;32L;51L;48L;49L;32L;77L;111L;118L;101L;100L;32L;80L;101L;114L;109L;97L;110L;101L;110L;116L;108L;121L;13L;10L;83L;101L;114L;118L;101L;114L;58L;32L;86L;97L;114L;110L;105L;115L;104L;13L;10L;82L;101L;116L;114L;121L;45L;65L;102L;116L;101L;114L;58L;32L;48L;13L;10L;67L;111L;110L;116L;101L;110L;116L;45L;76L;101L;110L;103L;116L;104L;58L;32L;48L;13L;10L;76L;111L;99L;97L;116L;105L;111L;110L;58L;32L;104L;116L;116L;112L;115L;58L;47L;47L;119L;119L;119L;46L;110L;121L;116L;105L;109L;101L;115L;46L;99L;111L;109L;47L;13L;10L;65L;99L;99L;101L;112L;116L;45L;82L;97L;110L;103L;101L;115L;58L;32L;98L;121L;116L;101L;115L;13L;10L;68L;97L;116L;101L;58L;32L;84L;104L;117L;44L;32L;49L;50L;32L;74L;117L;108L;32L;50L;48L;49L;56L;32L;48L;49L;58L;52L;54L;58L;49L;57L;32L;71L;77L;84L;13L;10L;88L;45L;83L;101L;114L;118L;101L;100L;45L;66L;121L;58L;32L;99L;97L;99L;104L;101L;45L;98L;111L;115L;56L;50L;51L;48L;45L;66L;79L;83L;13L;10L;88L;45L;67L;97L;99L;104L;101L;58L;32L;72L;73L;84L;13L;10L;88L;45L;67L;97L;99L;104L;101L;45L;72L;105L;116L;115L;58L;32L;48L;13L;10L;88L;45L;70L;114L;97L;109L;101L;45L;79L;112L;116L;105L;111L;110L;115L;58L;32L;68L;69L;78L;89L;13L;10L;67L;111L;110L;110L;101L;99L;116L;105L;111L;110L;58L;32L;99L;108L;111L;115L;101L;13L;10L;88L;45L;65L;80L;73L;45L;86L;101L;114L;115L;105L;111L;110L;58L;32L;70L;45L;48L;13L;10L;13L;10L|]

let http_response_tcp_encode_338_input = must (Fiat4Mirage.fiat_tcp_decode 338 http_response_tcp_decode_338_input (ArrayVector.of_array [|151L;101L;129L;164L|]) (ArrayVector.of_array [|192L;168L;1L;109L|]) (338L))

let ntp_request_ether_decode_90_input = ArrayVector.of_array [|80L;199L;191L;62L;218L;205L;72L;81L;183L;14L;152L;89L;8L;0L;69L;0L;0L;76L;42L;91L;64L;0L;64L;17L;104L;140L;192L;168L;1L;109L;132L;163L;97L;1L;0L;123L;0L;123L;0L;56L;213L;93L;227L;0L;3L;250L;0L;1L;0L;0L;0L;1L;0L;0L;0L;0L;0L;0L;0L;0L;0L;0L;0L;0L;0L;0L;0L;0L;0L;0L;0L;0L;0L;0L;0L;0L;0L;0L;0L;0L;0L;0L;222L;241L;103L;36L;233L;43L;107L;49L|]

let ntp_request_ether_encode_90_input = must (Fiat4Mirage.fiat_ethernet_decode 90 ntp_request_ether_decode_90_input 90)

let ntp_request_ip_decode_76_input = ArrayVector.of_array [|69L;0L;0L;76L;42L;91L;64L;0L;64L;17L;104L;140L;192L;168L;1L;109L;132L;163L;97L;1L;0L;123L;0L;123L;0L;56L;213L;93L;227L;0L;3L;250L;0L;1L;0L;0L;0L;1L;0L;0L;0L;0L;0L;0L;0L;0L;0L;0L;0L;0L;0L;0L;0L;0L;0L;0L;0L;0L;0L;0L;0L;0L;0L;0L;0L;0L;0L;0L;222L;241L;103L;36L;233L;43L;107L;49L|]

let ntp_request_ip_encode_76_input = must (Fiat4Mirage.fiat_ipv4_decode 76 ntp_request_ip_decode_76_input)

let ntp_request_udp_decode_56_input = ArrayVector.of_array [|0L;123L;0L;123L;0L;56L;213L;93L;227L;0L;3L;250L;0L;1L;0L;0L;0L;1L;0L;0L;0L;0L;0L;0L;0L;0L;0L;0L;0L;0L;0L;0L;0L;0L;0L;0L;0L;0L;0L;0L;0L;0L;0L;0L;0L;0L;0L;0L;222L;241L;103L;36L;233L;43L;107L;49L|]

let ntp_request_udp_encode_56_input = must (Fiat4Mirage.fiat_udp_decode 56 ntp_request_udp_decode_56_input (ArrayVector.of_array [|192L;168L;1L;109L|]) (ArrayVector.of_array [|132L;163L;97L;1L|]) (56L))

let ntp_response_ether_decode_90_input = ArrayVector.of_array [|72L;81L;183L;14L;152L;89L;80L;199L;191L;62L;218L;205L;8L;0L;69L;32L;0L;76L;130L;236L;0L;0L;54L;17L;89L;219L;132L;163L;97L;1L;192L;168L;1L;109L;0L;123L;0L;123L;0L;56L;247L;218L;28L;1L;13L;227L;0L;0L;0L;16L;0L;0L;0L;32L;78L;73L;83L;84L;222L;241L;102L;203L;0L;0L;0L;0L;222L;241L;103L;36L;233L;43L;107L;49L;222L;241L;103L;36L;241L;94L;157L;42L;222L;241L;103L;36L;241L;94L;166L;251L|]

let ntp_response_ether_encode_90_input = must (Fiat4Mirage.fiat_ethernet_decode 90 ntp_response_ether_decode_90_input 90)

let ntp_response_ip_decode_76_input = ArrayVector.of_array [|69L;32L;0L;76L;130L;236L;0L;0L;54L;17L;89L;219L;132L;163L;97L;1L;192L;168L;1L;109L;0L;123L;0L;123L;0L;56L;247L;218L;28L;1L;13L;227L;0L;0L;0L;16L;0L;0L;0L;32L;78L;73L;83L;84L;222L;241L;102L;203L;0L;0L;0L;0L;222L;241L;103L;36L;233L;43L;107L;49L;222L;241L;103L;36L;241L;94L;157L;42L;222L;241L;103L;36L;241L;94L;166L;251L|]

let ntp_response_ip_encode_76_input = must (Fiat4Mirage.fiat_ipv4_decode 76 ntp_response_ip_decode_76_input)

let ntp_response_udp_decode_56_input = ArrayVector.of_array [|0L;123L;0L;123L;0L;56L;247L;218L;28L;1L;13L;227L;0L;0L;0L;16L;0L;0L;0L;32L;78L;73L;83L;84L;222L;241L;102L;203L;0L;0L;0L;0L;222L;241L;103L;36L;233L;43L;107L;49L;222L;241L;103L;36L;241L;94L;157L;42L;222L;241L;103L;36L;241L;94L;166L;251L|]

let ntp_response_udp_encode_56_input = must (Fiat4Mirage.fiat_udp_decode 56 ntp_response_udp_decode_56_input (ArrayVector.of_array [|132L;163L;97L;1L|]) (ArrayVector.of_array [|192L;168L;1L;109L|]) (56L))

let () =
  Core.Command.run (Bench.make_command [
    Bench.Test.create ~name:"arp_request_ether_encode_42"
      (fun () -> ignore (must (Fiat4Mirage.fiat_ethernet_encode 4096 arp_request_ether_encode_42_input (ArrayVector.of_array buf))));
    Bench.Test.create ~name:"arp_request_ether_decode_42"
      (fun () -> ignore (must (Fiat4Mirage.fiat_ethernet_decode 42 arp_request_ether_decode_42_input 42)));
    Bench.Test.create ~name:"arp_request_arp_encode_28"
      (fun () -> ignore (must (Fiat4Mirage.fiat_arp_encode 4096 arp_request_arp_encode_28_input (ArrayVector.of_array buf))));
    Bench.Test.create ~name:"arp_request_arp_decode_28"
      (fun () -> ignore (must (Fiat4Mirage.fiat_arp_decode 28 arp_request_arp_decode_28_input)));
    Bench.Test.create ~name:"arp_response_ether_encode_42"
      (fun () -> ignore (must (Fiat4Mirage.fiat_ethernet_encode 4096 arp_response_ether_encode_42_input (ArrayVector.of_array buf))));
    Bench.Test.create ~name:"arp_response_ether_decode_42"
      (fun () -> ignore (must (Fiat4Mirage.fiat_ethernet_decode 42 arp_response_ether_decode_42_input 42)));
    Bench.Test.create ~name:"arp_response_arp_encode_28"
      (fun () -> ignore (must (Fiat4Mirage.fiat_arp_encode 4096 arp_response_arp_encode_28_input (ArrayVector.of_array buf))));
    Bench.Test.create ~name:"arp_response_arp_decode_28"
      (fun () -> ignore (must (Fiat4Mirage.fiat_arp_decode 28 arp_response_arp_decode_28_input)));
    Bench.Test.create ~name:"http_request_ether_encode_141"
      (fun () -> ignore (must (Fiat4Mirage.fiat_ethernet_encode 4096 http_request_ether_encode_141_input (ArrayVector.of_array buf))));
    Bench.Test.create ~name:"http_request_ether_decode_141"
      (fun () -> ignore (must (Fiat4Mirage.fiat_ethernet_decode 141 http_request_ether_decode_141_input 141)));
    Bench.Test.create ~name:"http_request_ip_encode_127"
      (fun () -> ignore (must (Fiat4Mirage.fiat_ipv4_encode 4096 http_request_ip_encode_127_input (ArrayVector.of_array buf))));
    Bench.Test.create ~name:"http_request_ip_decode_127"
      (fun () -> ignore (must (Fiat4Mirage.fiat_ipv4_decode 127 http_request_ip_decode_127_input)));
    Bench.Test.create ~name:"http_request_tcp_encode_107"
      (fun () -> ignore (must (Fiat4Mirage.fiat_tcp_encode 4096 http_request_tcp_encode_107_input (ArrayVector.of_array [|192L;168L;1L;109L|]) (ArrayVector.of_array [|151L;101L;129L;164L|]) (107L) (ArrayVector.of_array buf))));
    Bench.Test.create ~name:"http_request_tcp_decode_107"
      (fun () -> ignore (must (Fiat4Mirage.fiat_tcp_decode 107 http_request_tcp_decode_107_input (ArrayVector.of_array [|192L;168L;1L;109L|]) (ArrayVector.of_array [|151L;101L;129L;164L|]) (107L))));
    Bench.Test.create ~name:"http_response_ether_encode_372"
      (fun () -> ignore (must (Fiat4Mirage.fiat_ethernet_encode 4096 http_response_ether_encode_372_input (ArrayVector.of_array buf))));
    Bench.Test.create ~name:"http_response_ether_decode_372"
      (fun () -> ignore (must (Fiat4Mirage.fiat_ethernet_decode 372 http_response_ether_decode_372_input 372)));
    Bench.Test.create ~name:"http_response_ip_encode_358"
      (fun () -> ignore (must (Fiat4Mirage.fiat_ipv4_encode 4096 http_response_ip_encode_358_input (ArrayVector.of_array buf))));
    Bench.Test.create ~name:"http_response_ip_decode_358"
      (fun () -> ignore (must (Fiat4Mirage.fiat_ipv4_decode 358 http_response_ip_decode_358_input)));
    Bench.Test.create ~name:"http_response_tcp_encode_338"
      (fun () -> ignore (must (Fiat4Mirage.fiat_tcp_encode 4096 http_response_tcp_encode_338_input (ArrayVector.of_array [|151L;101L;129L;164L|]) (ArrayVector.of_array [|192L;168L;1L;109L|]) (338L) (ArrayVector.of_array buf))));
    Bench.Test.create ~name:"http_response_tcp_decode_338"
      (fun () -> ignore (must (Fiat4Mirage.fiat_tcp_decode 338 http_response_tcp_decode_338_input (ArrayVector.of_array [|151L;101L;129L;164L|]) (ArrayVector.of_array [|192L;168L;1L;109L|]) (338L))));
    Bench.Test.create ~name:"ntp_request_ether_encode_90"
      (fun () -> ignore (must (Fiat4Mirage.fiat_ethernet_encode 4096 ntp_request_ether_encode_90_input (ArrayVector.of_array buf))));
    Bench.Test.create ~name:"ntp_request_ether_decode_90"
      (fun () -> ignore (must (Fiat4Mirage.fiat_ethernet_decode 90 ntp_request_ether_decode_90_input 90)));
    Bench.Test.create ~name:"ntp_request_ip_encode_76"
      (fun () -> ignore (must (Fiat4Mirage.fiat_ipv4_encode 4096 ntp_request_ip_encode_76_input (ArrayVector.of_array buf))));
    Bench.Test.create ~name:"ntp_request_ip_decode_76"
      (fun () -> ignore (must (Fiat4Mirage.fiat_ipv4_decode 76 ntp_request_ip_decode_76_input)));
    Bench.Test.create ~name:"ntp_request_udp_encode_56"
      (fun () -> ignore (must (Fiat4Mirage.fiat_udp_encode 4096 ntp_request_udp_encode_56_input (ArrayVector.of_array [|192L;168L;1L;109L|]) (ArrayVector.of_array [|132L;163L;97L;1L|]) (56L) (ArrayVector.of_array buf))));
    Bench.Test.create ~name:"ntp_request_udp_decode_56"
      (fun () -> ignore (must (Fiat4Mirage.fiat_udp_decode 56 ntp_request_udp_decode_56_input (ArrayVector.of_array [|192L;168L;1L;109L|]) (ArrayVector.of_array [|132L;163L;97L;1L|]) (56L))));
    Bench.Test.create ~name:"ntp_response_ether_encode_90"
      (fun () -> ignore (must (Fiat4Mirage.fiat_ethernet_encode 4096 ntp_response_ether_encode_90_input (ArrayVector.of_array buf))));
    Bench.Test.create ~name:"ntp_response_ether_decode_90"
      (fun () -> ignore (must (Fiat4Mirage.fiat_ethernet_decode 90 ntp_response_ether_decode_90_input 90)));
    Bench.Test.create ~name:"ntp_response_ip_encode_76"
      (fun () -> ignore (must (Fiat4Mirage.fiat_ipv4_encode 4096 ntp_response_ip_encode_76_input (ArrayVector.of_array buf))));
    Bench.Test.create ~name:"ntp_response_ip_decode_76"
      (fun () -> ignore (must (Fiat4Mirage.fiat_ipv4_decode 76 ntp_response_ip_decode_76_input)));
    Bench.Test.create ~name:"ntp_response_udp_encode_56"
      (fun () -> ignore (must (Fiat4Mirage.fiat_udp_encode 4096 ntp_response_udp_encode_56_input (ArrayVector.of_array [|132L;163L;97L;1L|]) (ArrayVector.of_array [|192L;168L;1L;109L|]) (56L) (ArrayVector.of_array buf))));
    Bench.Test.create ~name:"ntp_response_udp_decode_56"
      (fun () -> ignore (must (Fiat4Mirage.fiat_udp_decode 56 ntp_response_udp_decode_56_input (ArrayVector.of_array [|132L;163L;97L;1L|]) (ArrayVector.of_array [|192L;168L;1L;109L|]) (56L))))
  ])
