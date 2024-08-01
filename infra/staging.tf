resource "google_compute_firewall" "allow-http-https" {
  name    = "allow-http-https"
  network = "default"

  allow {
    protocol = "tcp"
    ports    = ["80", "443", "22"]
  }

  // Allow traffic from everywhere to instances with an http-server tag
  source_ranges = ["0.0.0.0/0"]
  target_tags   = ["staging"]
}

resource "google_compute_address" "staging-external-address" {
  name = "staging-ip"
}

resource "google_compute_instance" "staging-vm" {
  name         = "staging-vm"
  machine_type = "n1-standard-1"
  tags         = ["staging"]

  allow_stopping_for_update = true

  metadata = {
    sshKeys = file("./ssh_keys")
  }

  boot_disk {
    initialize_params {
      image = "debian-cloud/debian-11"
    }
  }

  network_interface {
    network = "default"
    access_config {
      nat_ip = google_compute_address.staging-external-address.address
    }
  }
}

output "external-ip" {
  value = google_compute_address.staging-external-address.address
}
