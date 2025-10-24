import socket
import time

# Create a UDP socket
sock = socket.socket(socket.AF_INET, socket.SOCK_DGRAM)

# Bind to the specified IP and port
server_address = ('172.18.6.212', 8080)
sock.bind(server_address)

print(f"UDP server listening on {server_address}")

# Loop to receive messages
while True:
    # Receive data (up to 1024 bytes)
    data, address = sock.recvfrom(1024)
    
    # Get high-precision timestamp in nanoseconds
    timestamp_us = time.time_ns()/1000  # Convert to microseconds
    
    # Decode and print the message and timestamp
    message = data.decode('utf-8')  # Assuming UTF-8 encoding; adjust if needed
    print(f"Received from {address}: '{message}' at {timestamp_us} us (precision: 1e-9 s)")